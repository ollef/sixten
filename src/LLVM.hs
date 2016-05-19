{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, OverloadedStrings, ViewPatterns #-}
module LLVM where

import Control.Monad.State
import Data.Bifunctor
import qualified Data.Foldable as Foldable
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.List
import Data.Monoid
import Data.String
import qualified Data.Text as Text
import Data.Text(Text)

import Util
import Syntax.Hint

type B = Text

(<+>) :: B -> B -> B
x <+> y
  | Text.null x = y
  | Text.null y = x
  | otherwise = x <> " " <> y
infixr 6 <+>

-------------------------------------------------------------------------------
-- * The generation type
-------------------------------------------------------------------------------
data LLVMState = LLVMState
  { boundNames :: HashSet B
  , freeNames :: [B]
  , instructions :: [B]
  }

runLLVM :: State LLVMState a -> (a, [B])
runLLVM = second (reverse . instructions) . flip runState LLVMState
  { boundNames = mempty
  , freeNames = do
    n <- [(0 :: Int)..]
    c <- ['a'..'z']
    return $ "%" <> fromString (c : if n == 0 then "" else show n)
  , instructions = mempty
  }

emit :: MonadState LLVMState m => Instr a -> m ()
emit b = modify $ \s -> s { instructions = unInstr ("  " <> b) : instructions s }

emitLabel :: MonadState LLVMState m => Operand Label -> m ()
emitLabel l = modify $ \s -> s { instructions = (unOperand l <> ":") : instructions s }

-------------------------------------------------------------------------------
-- * Working with names
-------------------------------------------------------------------------------
percent :: B -> B
percent b | Text.head b == '%' = b
percent b = "%" <> b

freshenName :: MonadState LLVMState m => B -> m B
freshenName (percent -> name) = do
  bnames <- gets boundNames
  let candidates = name : [name <> shower n | n <- [(1 :: Int)..]]
      actualName = head $ filter (not . (`HashSet.member` bnames)) candidates
      bnames' = HashSet.insert actualName bnames
  modify $ \s -> s { boundNames = bnames' }
  return actualName

freshName :: MonadState LLVMState m => m B
freshName = do
  name:fnames <- gets freeNames
  modify $ \s -> s { freeNames = fnames }
  freshenName name

freshWithHint :: MonadState LLVMState m => NameHint -> m B
freshWithHint (Hint (Just name)) = freshenName name
freshWithHint (Hint Nothing) = freshName

-------------------------------------------------------------------------------
-- * Operands
-------------------------------------------------------------------------------
newtype Operand a = Operand { unOperand :: B } deriving (IsString, Monoid)
newtype Instr a = Instr { unInstr :: B } deriving (IsString, Monoid)
data Ptr
data Fun
data Label

align :: B
align = "8"

integerT, pointerT :: B
integerT = "i64"
pointerT = integerT <> "*"

ptrSize :: Operand Int
ptrSize = "8"

integer :: Operand Int -> B
integer (Operand b) = integerT <+> b

pointer :: Operand Ptr -> B
pointer (Operand b) = pointerT <+> b

label :: Operand Label -> B
label (Operand b) = "label" <+> b

-------------------------------------------------------------------------------
-- * Instructions
-------------------------------------------------------------------------------
add :: Operand Int -> Operand Int -> Instr Int
add x y = Instr $ "add" <+> integer x <> "," <+> unOperand y

callFun :: (Foldable f, Functor f) => Operand Fun -> f (Operand Ptr) -> Instr ()
callFun name xs = Instr
  $ "call" <+> "void" <+> unOperand name <> "(" <> Foldable.fold (intersperse ", " $ Foldable.toList $ pointer <$> xs) <> ")"

(=:) :: MonadState LLVMState m => NameHint -> Instr a -> m (Operand a)
h =: i = do
  x <- freshWithHint h
  emit $ Instr $ x <+> "=" <+> unInstr i
  return $ Operand x
infixr 6 =:

adds :: (MonadState LLVMState m, Foldable f) => f (Operand Int) -> m [Operand Int]
adds = fmap (reverse . fst) . Foldable.foldlM go ([], "0")
  where
    go (ys, v) o = do
      name <- mempty =: add v o
      return (v : ys, name)

memcpy
  :: Operand Ptr
  -> Operand Ptr
  -> Operand Int
  -> Instr ()
memcpy dst src sz = Instr
  $ "call void @llvm.memcpy.p0i8.p0i8.i64(i8* bitcast ("
  <> pointer dst <+> "to i8*)," <+> "i8* bitcast ("
  <> pointer src <+> "to i8*),"
  <+> integer sz <> ", i64" <+> align <> ", i1 false)"

getElementPtr :: Operand Ptr -> Operand Int -> Instr Ptr
getElementPtr x i = Instr $ "getelementptr" <+> integerT <> "," <+> pointer x <> "," <+> integer i

alloca :: Operand Int -> Instr Ptr
alloca sz = Instr $ "alloca" <+> integerT <> "," <+> integer sz <> ", align" <+> align

branch :: Operand Label -> Instr ()
branch l = Instr $ "br" <+> label l

load :: Operand Ptr -> Instr Int
load x = Instr $ "load" <+> integerT <> "," <+> pointer x

store :: Operand Int -> Operand Ptr -> Instr Int
store x p = Instr $ "store" <+> integer x <> "," <+> pointer p

switch :: Operand Int -> Operand Label -> [(Int, Operand Label)] -> Instr ()
switch e def brs = Instr
  $ "switch" <+> integer e <> "," <+> label def
  <+> "[" <> Foldable.fold (intersperse ", " $ (\(i, l) -> integer (shower i) <> "," <+> label l) <$> brs)
  <> "]"

phiPtr :: [(Operand Ptr, Operand Label)] -> Instr Ptr
phiPtr xs = Instr
  $ "phi" <+> pointerT
  <+> Foldable.fold (intersperse ", " $ (\(v, l) -> "[" <> pointer v <> "," <+> label l <> "]") <$> xs)

phiInt :: [(Operand Int, Operand Label)] -> Instr Int
phiInt xs = Instr
  $ "phi" <+> integerT
  <+> Foldable.fold (intersperse ", " $ (\(v, l) -> "[" <> integer v <> "," <+> label l <> "]") <$> xs)

bitcastToFun :: Operand Ptr -> Int -> Instr Fun
bitcastToFun p arity = Instr
  $ "bitcast" <+> pointer p <+> "to" <+> "void (" <> Foldable.fold (replicate (arity - 1) (pointerT <> ", ")) <> pointerT <> ")"

exit :: Int -> Instr ()
exit n = Instr $ "call void @exit(i32" <+> shower n <> ")"

retVoid :: Instr ()
retVoid = Instr "ret void"
