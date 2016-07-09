{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, OverloadedStrings #-}
module LLVM where

import Control.Applicative
import Control.Monad.State
import Data.Bifunctor
import Data.Char
import qualified Data.Foldable as Foldable
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.List
import Data.Monoid
import Data.String
import qualified Data.Text as Text
import Data.Text(Text)
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Util
import Syntax.Direction
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
    return $ fromString (c : if n == 0 then "" else show n)
  , instructions = mempty
  }

emitRaw :: MonadState LLVMState m => Instr a -> m ()
emitRaw b = modify $ \s -> s { instructions = unInstr b : instructions s }

emit :: MonadState LLVMState m => Instr a -> m ()
emit b = emitRaw ("  " <> b)

emitLabel :: MonadState LLVMState m => Operand Label -> m ()
emitLabel l
  = modify
  -- Hackish way to remove the "%"
  $ \s -> s { instructions = (Text.drop 1 (unOperand l) <> ":") : instructions s }

-------------------------------------------------------------------------------
-- * Working with names
-------------------------------------------------------------------------------
escape :: B -> B
escape b
  | validIdent b = b
  | otherwise = "\"" <> escapeQuotes b <> "\""

escapeQuotes :: B -> B
escapeQuotes = Text.concatMap go
  where
    go '"' = "\\22"
    go c = Text.singleton c

validIdent :: B -> Bool
validIdent str1 = case Text.uncons str1 of
  Nothing -> False
  Just (b, str2) -> startChar b && Text.all contChar str2
  where
    startChar c = 'a' <= c && c <= 'z'
               || 'A' <= c && c <= 'Z'
               || c `elem` ("-$._" :: String)
    contChar c = startChar c || isDigit c


freshenName :: MonadState LLVMState m => B -> m B
freshenName name = do
  bnames <- gets boundNames
  let candidates = name : [name <> shower n | n <- [(1 :: Int)..]]
      actualName = head $ filter (not . (`HashSet.member` bnames)) candidates
      bnames' = HashSet.insert actualName bnames
  modify $ \s -> s { boundNames = bnames' }
  return $ "%" <> escape actualName

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
newtype Operand a = Operand B deriving (Show, IsString, Monoid)
unOperand :: Operand a -> B
unOperand (Operand b) = b
newtype Instr a = Instr B deriving (Show, IsString, Monoid)
unInstr :: Instr a -> B
unInstr (Instr b) = b
data Ptr
data Fun
data Label

align :: B
align = "8"

integerT, pointerT, voidT :: B
integerT = "i64"
pointerT = integerT <> "*"
voidT = "void"

ptrSize :: Operand Int
ptrSize = "8"

global :: B -> Operand a
global b = Operand $ "@" <> b

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

mul :: Operand Int -> Operand Int -> Instr Int
mul x y = Instr $ "mul" <+> integer x <> "," <+> unOperand y

callFun :: (Foldable f, Functor f) => Operand Fun -> f (Operand Ptr) -> Instr ()
callFun name xs = Instr
  $ "call" <+> voidT <+> unOperand name <> "(" <> Foldable.fold (intersperse ", " $ Foldable.toList $ pointer <$> xs) <> ")"

(=:) :: MonadState LLVMState m => NameHint -> Instr a -> m (Operand a)
h =: i = do
  x <- freshWithHint h
  emit $ Instr $ x <+> "=" <+> unInstr i
  return $ Operand x
infixr 6 =:

adds
  :: (MonadState LLVMState m, Foldable f)
  => f (Operand Int)
  -> m ([Operand Int], Operand Int)
adds = fmap (first reverse) . Foldable.foldlM go ([], "0")
  where
    go (ys, v) o = do
      name <- mempty =: add v o
      return (v : ys, name)

memcpy
  :: MonadState LLVMState m
  => Operand Ptr
  -> Operand Ptr
  -> Operand Int
  -> m ()
memcpy dst src sz = do
  src' <- nameHint "src" =: Instr ("bitcast" <+> pointer src <+> "to i8*")
  dst' <- nameHint "dst" =: Instr ("bitcast" <+> pointer dst <+> "to i8*")
  emit $ Instr
       $ "call" <+> voidT <+> "@llvm.memcpy.p0i8.p0i8.i64(i8*"
       <+> unOperand dst' <> ", i8*" <+> unOperand src' <> ","
       <+> integer sz <> ", i32" <+> align <> ", i1 false)"

wordcpy
  :: MonadState LLVMState m
  => Operand Ptr
  -> Operand Ptr
  -> Operand Int
  -> m ()
wordcpy dst src wordSize = do
  byteSize <- nameHint "byte-size" =: mul wordSize ptrSize
  memcpy dst src byteSize

getElementPtr :: Operand Ptr -> Operand Int -> Instr Ptr
getElementPtr x i = Instr $ "getelementptr" <+> integerT <> "," <+> pointer x <> "," <+> integer i

alloca :: Operand Int -> Instr Ptr
alloca sz = Instr $ "alloca" <+> integerT <> "," <+> integer sz <> ", align" <+> align

intToPtr :: Operand Int -> Instr Ptr
intToPtr i = Instr $ "inttoptr" <+> integer i <+> "to" <+> pointerT

ptrToInt :: Operand Ptr -> Instr Int
ptrToInt p = Instr $ "ptrtoint" <+> pointer p <+> "to" <+> integerT

branch :: Operand Label -> Instr ()
branch l = Instr $ "br" <+> label l

load :: Operand Ptr -> Instr Int
load x = Instr $ "load" <+> integerT <> "," <+> pointer x

store :: Operand Int -> Operand Ptr -> Instr ()
store x p = Instr $ "store" <+> integer x <> "," <+> pointer p

switch :: Operand Int -> Operand Label -> [(Int, Operand Label)] -> Instr ()
switch e def brs = Instr
  $ "switch" <+> integer e <> "," <+> label def
  <+> "[" <> Foldable.fold (intersperse " " $ (\(i, l) -> integer (shower i) <> "," <+> label l) <$> brs)
  <> "]"

phiPtr :: [(Operand Ptr, Operand Label)] -> Instr Ptr
phiPtr xs = Instr
  $ "phi" <+> pointerT
  <+> Foldable.fold (intersperse ", " $ (\(v, l) -> "[" <> unOperand v <> "," <+> unOperand l <> "]") <$> xs)

phiInt :: [(Operand Int, Operand Label)] -> Instr Int
phiInt xs = Instr
  $ "phi" <+> integerT
  <+> Foldable.fold (intersperse ", " $ (\(v, l) -> "[" <> unOperand v <> "," <+> unOperand l <> "]") <$> xs)

bitcastToFun :: Operand Int -> Direction -> Vector Direction -> Instr Fun
bitcastToFun i retDir ds = Instr
  $ "bitcast" <+> integer i <+> "to"
  <+> retType <+> "(" <> Foldable.fold (intersperse ", " $ go <$> Vector.toList ds <|> retArg) <> ")"
  where
    (retType, retArg) = case retDir of
      Direct -> (integerT, mempty)
      Indirect -> (voidT, pure pointerT)
    go Direct = integerT
    go Indirect = pointerT


exit :: Int -> Instr ()
exit n = Instr $ "call" <+> voidT <+> "@exit(i32" <+> shower n <> ")"

returnVoid :: Instr ()
returnVoid = Instr $ "ret" <+> voidT

returnInt :: Operand Int -> Instr ()
returnInt o = Instr $ "ret" <+> integer o

unreachable :: Instr ()
unreachable = Instr "unreachable"
