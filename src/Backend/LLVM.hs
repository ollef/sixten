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
import Data.Maybe
import Data.Monoid
import Data.String
import qualified Data.Text as Text
import Data.Text(Text)
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Word

import Backend.Target(Target)
import qualified Backend.Target as Target
import qualified Pretty
import Syntax.Direction
import Syntax.Hint
import Syntax.Name
import Util
import Util.Tsil

-------------------------------------------------------------------------------
-- * Configs
-------------------------------------------------------------------------------
data Config = Config { cfgAlign, cfgPtrSize, cfgIntegerT, cfgPointerT :: Text }

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
      { cfgAlign = shower $ Target.ptrAlign t
      , cfgPtrSize = shower $ Target.ptrBytes t
      , cfgIntegerT = "i" <> shower (Target.intBits t)
      , cfgPointerT = "i8*"
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

align, voidT, integerT, byteT, pointerT :: C
-- ptrSize = C cfgPtrSize
align = C cfgAlign
voidT = "void"
integerT = C cfgIntegerT
byteT = C $ const "i8"
pointerT = C cfgPointerT

data Direct = Void | Int | Array
  deriving (Eq, Ord, Show)

directType :: Size -> Direct
directType 0 = Void
directType sz | sz <= 8 = Int
directType _ = Array

directT :: Size -> C
directT sz = case directType sz of
  Void -> "void"
  Int -> "i" <> shower (sz * 8)
  Array -> "[" <> shower sz <+> "x" <+> "i8]"

indirectT :: C
indirectT = pointerT

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
  , target :: Target
  , boundNames :: HashSet Text
  , freeNames :: [Text]
  , currentLabel :: Operand Label
  , instructions :: Tsil Text
  }

runLLVM :: State LLVMState a -> Target -> (a, [Text])
runLLVM s t = second (Foldable.toList . instructions) $ runState s LLVMState
  { config = targetConfig t
  , target = t
  , boundNames = mempty
  , freeNames = do
    n <- [(0 :: Int)..]
    c <- ['a'..'z']
    return $ fromString (c : if n == 0 then "" else show n)
  , currentLabel = error "no label"
  , instructions = mempty
  }

emitRaw :: MonadState LLVMState m => Instr a -> m ()
emitRaw i = modify $ \s -> s { instructions = Snoc (instructions s) $ unC (unInstr i) (config s) }

emit :: MonadState LLVMState m => Instr a -> m ()
emit b = emitRaw ("  " <> b)

emitLabel :: MonadState LLVMState m => Operand Label -> m ()
emitLabel l
  = modify
  -- Hackish way to remove the "%"
  $ \s -> s
  { instructions = Snoc (instructions s) $ Text.drop 1 (unC (unOperand l) (config s)) <> ":"
  , currentLabel = l
  }

-------------------------------------------------------------------------------
-- * Working with names
-------------------------------------------------------------------------------
escape :: Text -> Text
escape b
  | validIdent b = b
  | otherwise = "\"" <> escapeQuotes b <> "\""

escapeQuotes :: Text -> Text
escapeQuotes = Text.concatMap go
  where
    go '"' = "\\22"
    go c = Text.singleton c

validIdent :: Text -> Bool
validIdent str1 = case Text.uncons str1 of
  Nothing -> False
  Just (b, str2) -> startChar b && Text.all contChar str2
  where
    startChar c = 'a' <= c && c <= 'z'
               || 'A' <= c && c <= 'Z'
               || c `elem` ("-$._" :: String)
    contChar c = startChar c || isDigit c

freshenName :: MonadState LLVMState m => Text -> m Text
freshenName name = do
  bnames <- gets boundNames
  let candidates = name : [name <> shower n | n <- [(1 :: Int)..]]
      actualName = head $ filter (not . (`HashSet.member` bnames)) candidates
      bnames' = HashSet.insert actualName bnames
  modify $ \s -> s { boundNames = bnames' }
  return $ "%" <> escape actualName

freshName :: MonadState LLVMState m => m Text
freshName = do
  name:fnames <- gets freeNames
  modify $ \s -> s { freeNames = fnames }
  freshenName name

freshWithHint :: MonadState LLVMState m => NameHint -> m Text
freshWithHint (NameHint (Hint (Just (Name name)))) = freshenName name
freshWithHint (NameHint (Hint Nothing)) = freshName

freshLabel :: MonadState LLVMState m => Text -> m (Operand Label)
freshLabel name = Operand . text <$> freshenName name

-------------------------------------------------------------------------------
-- * Operands
-------------------------------------------------------------------------------
newtype Operand a = Operand C deriving (Show, IsString, Monoid)

unOperand :: Operand a -> C
unOperand (Operand b) = b

newtype Instr a = Instr C deriving (Show, IsString, Monoid)

unInstr :: Instr a -> C
unInstr (Instr c) = c

data Ptr
data PtrPtr
data Fun
data Label

global :: Name -> Operand a
global (Name b) = Operand $ "@" <> text (escape b)

integer :: Operand Int -> C
integer o = integerT <+> unOperand o

byte :: Operand Word8 -> C
byte o = byteT <+> unOperand o

pointer :: Operand Ptr -> C
pointer o = pointerT <+> unOperand o

direct :: Size -> Operand Direct -> C
direct sz o = directT sz <+> unOperand o

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
adds = fmap (first Foldable.toList) . Foldable.foldlM go (Nil, "0")
  where
    go (ys, v) o = do
      name <- mempty =: add v o
      return (Snoc ys v, name)

memcpy
  :: MonadState LLVMState m
  => Operand Ptr
  -> Operand Ptr
  -> Operand Int
  -> m ()
memcpy dst src sz = emit $ Instr
  $ "call" <+> voidT <+> "@llvm.memcpy.p0i8.p0i8." <> integerT <> "("
  <> pointer dst <> "," <+> pointer src <> ","
  <+> integer sz <> ", i32" <+> align <> ", i1 false)"

gcAlloc
  :: MonadState LLVMState m
  => Operand Int
  -> m (Operand Ptr)
gcAlloc byteSize = do
  byteRef <- "byteref" =: Instr ("call i8* @GC_malloc(" <> integer byteSize <> ")")
  "ref" =: Instr ("bitcast" <+> "i8*" <+> unOperand byteRef <+> "to" <+> pointerT)

getElementPtr
  :: Operand Ptr
  -> Operand Int
  -> Instr Ptr
getElementPtr x i = Instr $ "getelementptr i8," <+> pointer x <> "," <+> integer i

alloca
  :: Operand Int
  -> Instr Ptr
alloca sz = Instr $ "alloca i8," <+> integer sz <> ", align" <+> align

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

loadDirect
  :: MonadState LLVMState m
  => Size
  -> NameHint
  -> Operand Ptr
  -> m (Operand Direct)
loadDirect sz h o = case directType sz of
  Void -> return "0"
  Int -> nonVoidCase
  Array -> nonVoidCase
  where
    nonVoidCase = do
      directPtr <- "direct-ptr" =: Instr ("bitcast" <+> pointer o <+> "to" <+> directT sz <> "*")
      h =: Instr ("load" <+> directT sz <> "," <+> directT sz <> "*" <+> unOperand directPtr)

storeDirect
  :: MonadState LLVMState m
  => Size
  -> Operand Direct
  -> Operand Ptr
  -> m ()
storeDirect sz src dst = case directType sz of
  Void -> return ()
  Int -> nonVoidCase
  Array -> nonVoidCase
  where
    nonVoidCase = do
      directPtr <- "direct-ptr" =: Instr ("bitcast" <+> pointer dst <+> "to" <+> directT sz <> "*")
      emit $ Instr ("store" <+> direct sz src <> "," <+> directT sz <> "*" <+> unOperand directPtr)

loadPtr
  :: Operand PtrPtr
  -> Instr Ptr
loadPtr x = Instr $ "load" <+> pointerT <> "," <+> pointerT <> "*" <+> unOperand x

loadInt
  :: MonadState LLVMState m
  => NameHint
  -> Operand Ptr
  -> m (Operand Int)
loadInt h ptr = do
  intPtr <- "ptr" =: Instr ("bitcast" <+> pointer ptr <+> "to" <+> integerT <> "*")
  h =: Instr ("load" <+> integerT <> "," <+> integerT <> "*" <+> unOperand intPtr)

storeInt
  :: MonadState LLVMState m
  => Operand Int
  -> Operand Ptr
  -> m ()
storeInt x ptr = do
  intPtr <- "ptr" =: Instr ("bitcast" <+> pointer ptr <+> "to" <+> integerT <> "*")
  emit $ Instr $ "store" <+> integer x <> "," <+> integerT <> "*" <+> unOperand intPtr

storeByte
  :: MonadState LLVMState m
  => Operand Word8
  -> Operand Ptr
  -> m ()
storeByte x ptr = do
  intPtr <- "ptr" =: Instr ("bitcast" <+> pointer ptr <+> "to" <+> byteT <> "*")
  emit $ Instr $ "store" <+> byte x <> "," <+> byteT <> "*" <+> unOperand intPtr

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

switch8
  :: Operand Word8
  -> Operand Label
  -> [(Word8, Operand Label)]
  -> Instr ()
switch8 e def brs = Instr
  $ "switch" <+> byte e <> "," <+> label def
  <+> "[" <> Foldable.fold (intersperse " " $ (\(i, l) -> byte (shower i) <> "," <+> label l) <$> brs)
  <> "]"

phiPtr
  :: [(Operand Ptr, Operand Label)]
  -> Instr Ptr
phiPtr xs = Instr
  $ "phi" <+> pointerT
  <+> Foldable.fold (intersperse ", " $ (\(v, l) -> "[" <> unOperand v <> "," <+> unOperand l <> "]") <$> xs)

phiDirect
  :: Size
  -> [(Operand Direct, Operand Label)]
  -> Instr Direct
phiDirect sz xs = Instr
  $ "phi" <+> directT sz
  <+> Foldable.fold (intersperse ", " $ (\(v, l) -> "[" <> unOperand v <> "," <+> unOperand l <> "]") <$> xs)

undef :: Operand a
undef = Operand "undef"

bitcastToFun :: Operand Ptr -> RetDir -> Vector Direction -> Instr Fun
bitcastToFun i retDir ds = Instr
  $ "bitcast" <+> pointer i <+> "to"
  <+> functionT retDir ds <> "*"

bitcastFunToPtrExpr :: Operand Fun -> RetDir -> Vector Direction -> Operand Ptr
bitcastFunToPtrExpr i retDir ds = Operand
  $ "bitcast" <+> "(" <> functionT retDir ds <> "*" <+> unOperand i <+> "to" <+> pointerT <> ")"

function :: RetDir -> Maybe C -> Vector Direction -> C
function retDir mname ds = retType <+> fromMaybe mempty mname <> "(" <> Foldable.fold (intersperse ", " $ concat $ go <$> Vector.toList ds <|> [retParam]) <> ")"
  where
    (retType, retParam) = case retDir of
      ReturnDirect sz -> (directT sz, mempty)
      ReturnIndirect OutParam -> (voidT, pure pointerT)
      ReturnIndirect Projection -> (pointerT, mempty)
    go (Direct sz) = case directType sz of
      Void -> []
      Int -> [directT sz]
      Array -> [directT sz]
    go Indirect = [pointerT]

declareFun
  :: MonadState LLVMState m
  => RetDir
  -> Name
  -> Vector Direction
  -> m ()
declareFun retDir name ds
  = emitRaw $ Instr
  $ "declare" <+> function retDir (Just $ unOperand $ global name) ds

functionT :: RetDir -> Vector Direction -> C
functionT retDir = function retDir Nothing

exit :: Int -> Instr ()
exit n = Instr $ "call" <+> voidT <+> "@exit(i32" <+> shower n <> ")"

returnVoid :: Instr ()
returnVoid = Instr $ "ret" <+> voidT

returnDirect :: Size -> Operand Direct -> Instr ()
returnDirect 0 _ = Instr "ret void"
returnDirect sz o = Instr $ "ret" <+> direct sz o

returnPtr :: Operand Ptr -> Instr ()
returnPtr o = Instr $ "ret" <+> pointer o

unreachable :: Instr ()
unreachable = Instr "unreachable"
