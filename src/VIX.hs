{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, Rank2Types, TypeFamilies, OverloadedStrings #-}
module VIX where

import Control.Monad.Except
import Control.Monad.ST
import Control.Monad.State
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Lazy(HashMap)
import Data.HashSet(HashSet)
import Data.List as List
import Data.Monoid
import Data.String
import Data.Text(Text)
import qualified Data.Text.IO as Text
import Data.Void
import System.IO
import Text.Trifecta.Result(Err(Err), explain)

import Backend.Target
import Syntax
import Syntax.Abstract
import qualified Syntax.Sized.Lifted as Lifted
import Util

newtype Level = Level Int
  deriving (Eq, Num, Ord, Show)

instance Pretty Level where
  pretty (Level i) = pretty i

data VIXState = VIXState
  { vixLocation :: SourceLoc
  , vixContext :: HashMap QName (Definition Expr Void, Type Void)
  , vixModuleNames :: MultiHashMap ModuleName (Either QConstr QName)
  , vixConvertedSignatures :: HashMap QName Lifted.FunSignature
  , vixSignatures :: HashMap QName (Signature ReturnIndirect)
  , vixIndent :: !Int
  , vixFresh :: !Int
  , vixLevel :: !Level
  , vixLogHandle :: !Handle
  , vixVerbosity :: !Int
  , vixTarget :: Target
  }

emptyVIXState :: Target -> Handle -> Int -> VIXState
emptyVIXState target handle verbosity = VIXState
  { vixLocation = mempty
  , vixContext = mempty
  , vixModuleNames = mempty
  , vixConvertedSignatures = mempty
  , vixSignatures = mempty
  , vixIndent = 0
  , vixFresh = 0
  , vixLevel = Level 1
  , vixLogHandle = handle
  , vixVerbosity = verbosity
  , vixTarget = target
  }

newtype VIX a = VIX (ExceptT String (StateT VIXState IO) a)
  deriving (Functor, Applicative, Monad, MonadFix, MonadError String, MonadState VIXState, MonadIO)

liftST :: ST RealWorld a -> VIX a
liftST = VIX . liftIO . stToIO

unVIX
  :: VIX a
  -> ExceptT String (StateT VIXState IO) a
unVIX (VIX x) = x

runVIX
  :: VIX a
  -> Target
  -> Handle
  -> Int
  -> IO (Either String a)
runVIX vix target handle verbosity
  = evalStateT (runExceptT $ unVIX vix)
  $ emptyVIXState target handle verbosity

fresh :: VIX Int
fresh = do
  i <- gets vixFresh
  modify $ \s -> s {vixFresh = i + 1}
  return i

level :: VIX Level
level = gets vixLevel

enterLevel :: VIX a -> VIX a
enterLevel x = do
  l <- level
  modify $ \s -> s {vixLevel = l + 1}
  r <- x
  modify $ \s -> s {vixLevel = l}
  return r

located :: SourceLoc -> VIX a -> VIX a
located loc m = do
  oldLoc <- gets vixLocation
  modify $ \s -> s { vixLocation = loc }
  res <- m
  modify $ \s -> s { vixLocation = oldLoc }
  return res

currentLocation :: VIX SourceLoc
currentLocation = gets vixLocation

-------------------------------------------------------------------------------
-- Debugging
log :: Text -> VIX ()
log l = do
  h <- gets vixLogHandle
  liftIO $ Text.hPutStrLn h l

logVerbose :: Int -> Text -> VIX ()
logVerbose v l = whenVerbose v $ VIX.log l

modifyIndent :: (Int -> Int) -> VIX ()
modifyIndent f = modify $ \s -> s {vixIndent = f $ vixIndent s}

logPretty :: Pretty a => Int -> String -> a -> VIX ()
logPretty v s x = whenVerbose v $ do
  i <- gets vixIndent
  VIX.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide (pretty x)

logShow :: Show a => Int -> String -> a -> VIX ()
logShow v s x = whenVerbose v $ do
  i <- gets vixIndent
  VIX.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> fromString (show x)

whenVerbose :: Int -> VIX () -> VIX ()
whenVerbose i m = do
  v <- gets vixVerbosity
  when (v >= i) m

-------------------------------------------------------------------------------
-- Working with abstract syntax
addContext :: HashMap QName (Definition Expr Void, Type Void) -> VIX ()
addContext prog = modify $ \s -> s
  { vixContext = prog <> vixContext s
  }

throwLocated :: Doc -> VIX a
throwLocated x = do
  loc <- currentLocation
  throwError
    $ show
    $ explain loc
    $ Err (Just $ pretty x) mempty mempty mempty

definition :: QName -> VIX (Definition Expr v, Expr v)
definition name = do
  mres <- gets $ HashMap.lookup name . vixContext
  maybe (throwLocated $ "Not in scope: " <> pretty name)
        (return . bimap vacuous vacuous)
        mres

addModule
  :: ModuleName
  -> HashSet (Either QConstr QName)
  -> VIX ()
addModule m names = modify $ \s -> s
  { vixModuleNames = multiUnion (HashMap.singleton m names) $ vixModuleNames s
  }

qconstructor :: QConstr -> VIX (Type v)
qconstructor qc@(QConstr n c) = do
  (def, typ) <- definition n
  case def of
    DataDefinition dataDef _ -> do
      let qcs = quantifiedConstrTypes dataDef typ $ const Implicit
      case filter ((== c) . constrName) qcs of
        [] -> throwLocated $ "Not in scope: constructor " <> pretty qc
        [cdef] -> return $ constrType cdef
        _ -> throwLocated $ "Ambiguous constructor: " <> pretty qc
    Definition {} -> no
  where
    no = throwLocated $ "Not a data type: " <> pretty n

-------------------------------------------------------------------------------
-- Signatures
addConvertedSignatures
  :: HashMap QName Lifted.FunSignature
  -> VIX ()
addConvertedSignatures p
  = modify $ \s -> s { vixConvertedSignatures = p <> vixConvertedSignatures s }

convertedSignature
  :: QName
  -> VIX (Maybe Lifted.FunSignature)
convertedSignature name = gets $ HashMap.lookup name . vixConvertedSignatures

addSignatures
  :: HashMap QName (Signature ReturnIndirect)
  -> VIX ()
addSignatures p = modify $ \s -> s { vixSignatures = p <> vixSignatures s }

signature
  :: QName
  -> VIX (Signature ReturnIndirect)
signature name = do
  sigs <- gets vixSignatures
  mres <- gets $ HashMap.lookup name . vixSignatures
  maybe (throwError $ "Not in scope: signature for " ++ show name ++ show sigs)
        return
        mres

-------------------------------------------------------------------------------
-- General constructor queries
qconstructorIndex :: VIX (QConstr -> Maybe Int)
qconstructorIndex = do
  cxt <- gets vixContext
  return $ \(QConstr n c) -> do
    (DataDefinition (DataDef constrDefs) _, _) <- HashMap.lookup n cxt
    case constrDefs of
      [] -> Nothing
      [_] -> Nothing
      _ -> findIndex ((== c) . constrName) constrDefs

constrArity
  :: QConstr
  -> VIX Int
constrArity
  = fmap (teleLength . fst . pisView)
  . (qconstructor :: QConstr -> VIX (Expr Void))

constrIndex
  :: QConstr
  -> VIX Int
constrIndex qc@(QConstr n c) = do
  (DataDefinition (DataDef cs) _, _) <- definition n
  case List.findIndex ((== c) . constrName) cs of
    Just i -> return i
    Nothing -> throwError $ "Can't find index for " ++ show qc
