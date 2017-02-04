{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, OverloadedStrings #-}
module Backend.LLVM where

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

import Backend.Target
import qualified Pretty
import Syntax.Direction
import Syntax.Hint
import Syntax.Name
import Util

type B = Text

-------------------------------------------------------------------------------
-- * Configs
-------------------------------------------------------------------------------
data Config = Config { cfgAlign, cfgPtrSize, cfgIntegerT, cfgPointerT :: B }

prettyConfig :: Config
prettyConfig = Config
  { cfgAlign = "<align>"
  , cfgPtrSize = "<ptrSize>"
  , cfgIntegerT = "<integer>"
  , cfgPointerT = "<integer>*"
  }

targetConfig :: Target -> Config
targetConfig t = cfg
  where
    cfg = Config
      { cfgAlign = shower $ ptrAlign t
      , cfgPtrSize = shower $ ptrBytes t
      , cfgIntegerT = "i" <> shower (ptrBits t)
      , cfgPointerT = cfgIntegerT cfg <> "*"
      }

-------------------------------------------------------------------------------
-- * Config-dependent code
-------------------------------------------------------------------------------
newtype C = C (Config -> Text)
  deriving Monoid

instance Pretty.Pretty C where
  prettyM (C f) = Pretty.prettyM $ f prettyConfig

instance Eq C where
  C f == C g = f prettyConfig == g prettyConfig

instance Ord C where
  compare (C f) (C g) = compare (f prettyConfig) (g prettyConfig)

instance Show C where
  show (C f) = show $ f prettyConfig

text :: Text -> C
text = C . const

unC :: C -> Config -> Text
unC (C f) = f

instance IsString C where
  fromString = text . fromString

ptrSize :: Operand Int
ptrSize = Operand $ C cfgPtrSize
align, integerT, pointerT :: C
align = C cfgAlign
integerT = C cfgIntegerT
pointerT = C cfgPointerT

(<+>) :: C -> C -> C
C f <+> C g = C $ \c -> case (f c, g c) of
  (x, y)
    | Text.null x -> y
    | Text.null y -> x
    | otherwise -> x <> " " <> y
infixr 6 <+>

-------------------------------------------------------------------------------
-- * The generation type
-------------------------------------------------------------------------------
data LLVMState = LLVMState
  { config :: Config
  , boundNames :: HashSet B
  , freeNames :: [B]
  , currentLabel :: Operand Label
  , instructions :: [B]
  }

runLLVM :: State LLVMState a -> Target -> (a, [B])
runLLVM s t = second (reverse . instructions) $ runState s LLVMState
  { config = targetConfig t
  , boundNames = mempty
  , freeNames = do
    n <- [(0 :: Int)..]
    c <- ['a'..'z']
    return $ fromString (c : if n == 0 then "" else show n)
  , currentLabel = error "no label"
  , instructions = mempty
  }

emitRaw :: MonadState LLVMState m => Instr a -> m ()
emitRaw i = modify $ \s -> s { instructions = unC (unInstr i) (config s) : instructions s }

emit :: MonadState LLVMState m => Instr a -> m ()
emit b = emitRaw ("  " <> b)

emitLabel :: MonadState LLVMState m => Operand Label -> m ()
emitLabel l
  = modify
  -- Hackish way to remove the "%"
  $ \s -> s
  { instructions = (Text.drop 1 (unC (unOperand l) (config s)) <> ":") : instructions s
  , currentLabel = l
  }


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
freshWithHint (NameHint (Hint (Just (Name name)))) = freshenName name
freshWithHint (NameHint (Hint Nothing)) = freshName

-------------------------------------------------------------------------------
-- * Operands
-------------------------------------------------------------------------------
newtype Operand a = Operand C deriving (IsString, Monoid)

unOperand :: Operand a -> C
unOperand (Operand b) = b

newtype Instr a = Instr C deriving (IsString, Monoid)

unInstr :: Instr a -> C
unInstr (Instr c) = c

data Ptr
data PtrPtr
data Fun
data Label

voidT :: C
voidT = "void"

global :: Name -> Operand a
global (Name b) = Operand $ "@" <> text (escape b)

integer :: Operand Int -> C
integer o = integerT <+> unOperand o

pointer :: Operand Ptr -> C
pointer o = pointerT <+> unOperand o

label :: Operand Label -> C
label o = "label" <+> unOperand o

-------------------------------------------------------------------------------
-- * Instructions
-------------------------------------------------------------------------------
add :: Operand Int -> Operand Int -> Instr Int
add x y = Instr $ "add" <+> integer x <> "," <+> unOperand y

mul :: Operand Int -> Operand Int -> Instr Int
mul x y = Instr $ "mul" <+> integer x <> "," <+> unOperand y

(=:) :: MonadState LLVMState m => NameHint -> Instr a -> m (Operand a)
h =: i = do
  x <- text <$> freshWithHint h
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
  src' <- "src" =: Instr ("bitcast" <+> pointer src <+> "to i8*")
  dst' <- "dst" =: Instr ("bitcast" <+> pointer dst <+> "to i8*")
  emit $ Instr
    $ "call" <+> voidT <+> "@llvm.memcpy.p0i8.p0i8." <> integerT <> "(i8*"
    <+> unOperand dst' <> ", i8*" <+> unOperand src' <> ","
    <+> integer sz <> ", i32" <+> align <> ", i1 false)"

wordcpy
  :: MonadState LLVMState m
  => Operand Ptr
  -> Operand Ptr
  -> Operand Int
  -> m ()
wordcpy dst src wordSize = do
  byteSize <- "byte-size" =: mul wordSize ptrSize
  memcpy dst src byteSize

gcAlloc
  :: MonadState LLVMState m
  => Operand Int
  -> m (Operand Ptr)
gcAlloc wordSize = do
  byteSize <- "byte-size" =: mul wordSize ptrSize
  byteRef <- "byteref" =: Instr ("call i8* @GC_malloc(" <> integer byteSize <> ")")
  "ref" =: Instr ("bitcast" <+> "i8*" <+> unOperand byteRef <+> "to" <+> pointerT)

getElementPtr
  :: Operand Ptr
  -> Operand Int
  -> Instr Ptr
getElementPtr x i = Instr $ "getelementptr" <+> integerT <> "," <+> pointer x <> "," <+> integer i

alloca
  :: Operand Int
  -> Instr Ptr
alloca sz = Instr $ "alloca" <+> integerT <> "," <+> integer sz <> ", align" <+> align

intToPtr
  :: Operand Int
  -> Instr Ptr
intToPtr i = Instr $ "inttoptr" <+> integer i <+> "to" <+> pointerT

ptrToInt
  :: Operand Ptr
  -> Instr Int
ptrToInt p = Instr $ "ptrtoint" <+> pointer p <+> "to" <+> integerT

ptrToIntExpr
  :: Operand Ptr
  -> Operand Int
ptrToIntExpr p = Operand $ "ptrtoint" <+> "(" <> pointer p <+> "to" <+> integerT <> ")"

branch :: Operand Label -> Instr ()
branch l = Instr $ "br" <+> label l

load
  :: Operand Ptr
  -> Instr Int
load x = Instr $ "load" <+> integerT <> "," <+> pointer x

loadPtr
  :: Operand PtrPtr
  -> Instr Ptr
loadPtr x = Instr $ "load" <+> pointerT <> "," <+> pointerT <> "*" <+> unOperand x

store
  :: Operand Int
  -> Operand Ptr
  -> Instr ()
store x p = Instr $ "store" <+> integer x <> "," <+> pointer p

storePtr
  :: Operand Ptr
  -> Operand PtrPtr
  -> Instr ()
storePtr x p = Instr $ "store" <+> pointer x <> "," <+> pointerT <> "*" <+> unOperand p

switch
  :: Operand Int
  -> Operand Label
  -> [(Int, Operand Label)]
  -> Instr ()
switch e def brs = Instr
  $ "switch" <+> integer e <> "," <+> label def
  <+> "[" <> Foldable.fold (intersperse " " $ (\(i, l) -> integer (shower i) <> "," <+> label l) <$> brs)
  <> "]"

phiPtr
  :: [(Operand Ptr, Operand Label)]
  -> Instr Ptr
phiPtr xs = Instr
  $ "phi" <+> pointerT
  <+> Foldable.fold (intersperse ", " $ (\(v, l) -> "[" <> unOperand v <> "," <+> unOperand l <> "]") <$> xs)

phiInt
  :: [(Operand Int, Operand Label)]
  -> Instr Int
phiInt xs = Instr
  $ "phi" <+> integerT
  <+> Foldable.fold (intersperse ", " $ (\(v, l) -> "[" <> unOperand v <> "," <+> unOperand l <> "]") <$> xs)

bitcastToFun :: Operand Ptr -> RetDir -> Vector Direction -> Instr Fun
bitcastToFun i retDir ds = Instr
  $ "bitcast" <+> pointer i <+> "to"
  <+> retType <+> "(" <> Foldable.fold (intersperse ", " $ concat $ go <$> Vector.toList ds <|> [retArg]) <> ")*"
  where
    (retType, retArg) = case retDir of
      ReturnVoid -> (voidT, mempty)
      ReturnDirect -> (integerT, mempty)
      ReturnIndirect OutParam -> (voidT, pure pointerT)
      ReturnIndirect Projection -> (pointerT, mempty)
    go Void = []
    go Direct = [integerT]
    go Indirect = [pointerT]

bitcastFunToPtrExpr :: Operand Fun -> RetDir -> Vector Direction -> Operand Ptr
bitcastFunToPtrExpr i retDir ds = Operand
  $ "bitcast" <+> "(" <> retType <+> "(" <> Foldable.fold (intersperse ", " $ concat $ go <$> Vector.toList ds <|> [retArg]) <> ")*" <+> unOperand i <+> "to" <+> pointerT <> ")"
  where
    (retType, retArg) = case retDir of
      ReturnVoid -> (voidT, mempty)
      ReturnDirect -> (integerT, mempty)
      ReturnIndirect OutParam -> (voidT, pure pointerT)
      ReturnIndirect Projection -> (pointerT, mempty)
    go Void = []
    go Direct = [integerT]
    go Indirect = [pointerT]

exit :: Int -> Instr ()
exit n = Instr $ "call" <+> voidT <+> "@exit(i32" <+> shower n <> ")"

returnVoid :: Instr ()
returnVoid = Instr $ "ret" <+> voidT

returnInt :: Operand Int -> Instr ()
returnInt o = Instr $ "ret" <+> integer o

returnPtr :: Operand Ptr -> Instr ()
returnPtr o = Instr $ "ret" <+> pointer o

unreachable :: Instr ()
unreachable = Instr "unreachable"
