{-# LANGUAGE GeneralizedNewtypeDeriving, OverloadedStrings, ViewPatterns #-}
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
data GenState = GenState
  { boundNames :: HashSet B
  , freeNames :: [B]
  , instructions :: [B]
  }

runGen :: Gen a -> (a, [B])
runGen = second (reverse . instructions) . flip runState GenState
  { boundNames = mempty
  , freeNames = do
    n <- [(0 :: Int)..]
    c <- ['a'..'z']
    return $ "%" <> fromString (c : if n == 0 then "" else show n)
  , instructions = mempty
  }

type Gen a = State GenState a

emit :: Instr a -> Gen ()
emit b = modify $ \s -> s { instructions = (unInstr $ "  " <> b) : instructions s }

emitLabel :: Operand Label -> Gen ()
emitLabel l = modify $ \s -> s { instructions = (unOperand l <> ":") : instructions s }

-------------------------------------------------------------------------------
-- * Working with names
-------------------------------------------------------------------------------
percent :: B -> B
percent b | Text.head b == '%' = b
percent b = "%" <> b

freshenName :: B -> Gen B
freshenName (percent -> name) = do
  bnames <- gets boundNames
  let candidates = name : [name <> shower n | n <- [(1 :: Int)..]]
      actualName = head $ filter (not . (`HashSet.member` bnames)) candidates
      bnames' = HashSet.insert actualName bnames
  modify $ \s -> s { boundNames = bnames' }
  return actualName

freshName :: Gen B
freshName = do
  name:fnames <- gets freeNames
  modify $ \s -> s { freeNames = fnames }
  freshenName name

freshWithHint :: NameHint -> Gen B
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

intT, ptrT :: B
intT = "i64"
ptrT = intT <> "*"

ptrSize :: Operand Int
ptrSize = "8"

int :: Operand Int -> B
int (Operand b) = intT <+> b

ptr :: Operand Ptr -> B
ptr (Operand b) = ptrT <+> b

label :: Operand Label -> B
label (Operand b) = "label" <+> b

-------------------------------------------------------------------------------
-- * Instructions
-------------------------------------------------------------------------------
add :: Operand Int -> Operand Int -> Instr Int
add x y = Instr $ "add" <+> int x <> "," <+> unOperand y

callFun :: (Foldable f, Functor f) => Operand Fun -> f (Operand Ptr) -> Instr ()
callFun name xs = Instr
  $ "call" <+> "void" <+> unOperand name <> "(" <> Foldable.fold (intersperse ", " $ Foldable.toList $ ptr <$> xs) <> ")"

(=:) :: NameHint -> Instr a -> Gen (Operand a)
h =: i = do
  x <- freshWithHint h
  emit $ Instr $ x <+> "=" <+> unInstr i
  return $ Operand x
infixr 6 =:

adds :: Foldable f => f (Operand Int) -> Gen ([Operand Int], Operand Int)
adds = fmap (first reverse) . Foldable.foldlM go ([], "0")
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
  <> ptr dst <+> "to i8*)," <+> "i8* bitcast ("
  <> ptr src <+> "to i8*),"
  <+> int sz <> ", i64" <+> align <> ", i1 false)"

getElementPtr :: Operand Ptr -> Operand Int -> Instr Ptr
getElementPtr x i = Instr $ "getelementptr" <+> intT <> "," <+> ptr x <> "," <+> int i

alloca :: Operand Int -> Instr Ptr
alloca sz = Instr $ "alloca" <+> intT <> "," <+> int sz <> ", align" <+> align

br :: Operand Label -> Instr ()
br l = Instr $ "br" <+> label l

load :: Operand Ptr -> Instr Int
load x = Instr $ "load" <+> intT <> "," <+> ptr x

store :: Operand Int -> Operand Ptr -> Instr Int
store x p = Instr $ "store" <+> int x <> "," <+> ptr p

switch :: Operand Int -> Operand Label -> [(Int, Operand Label)] -> Instr ()
switch e def brs = Instr
  $ "switch" <+> int e <> "," <+> label def
  <+> "[" <> Foldable.fold (intersperse ", " $ (\(i, l) -> int (shower i) <> "," <+> label l) <$> brs)
  <> "]"

phiPtr :: [(Operand Ptr, Operand Label)] -> Instr Ptr
phiPtr xs = Instr
  $ "phi" <+> ptrT
  <+> Foldable.fold (intersperse ", " $ (\(v, l) -> "[" <> ptr v <> "," <+> label l <> "]") <$> xs)

phiInt :: [(Operand Int, Operand Label)] -> Instr Int
phiInt xs = Instr
  $ "phi" <+> intT
  <+> Foldable.fold (intersperse ", " $ (\(v, l) -> "[" <> int v <> "," <+> label l <> "]") <$> xs)

bitcastToFun :: Operand Ptr -> Int -> Instr Fun
bitcastToFun p arity = Instr
  $ "bitcast" <+> ptr p <+> "to" <+> "void (" <> Foldable.fold (replicate (arity - 1) (ptrT <> ", ")) <> ptrT <> ")"

exit :: Int -> Instr ()
exit n = Instr $ "call void @exit(i32" <+> shower n <> ")"

retVoid :: Instr ()
retVoid = Instr "ret void"
