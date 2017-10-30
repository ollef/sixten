{-# LANGUAGE ConstraintKinds, FlexibleContexts, GeneralizedNewtypeDeriving, OverloadedStrings #-}
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
import Data.Vector(Vector)
import Data.Void
import System.IO
import Text.Trifecta.Result(Err(Err), explain)

import Backend.Target
import Syntax
import Syntax.Abstract
import qualified Syntax.Sized.Lifted as Lifted
import Util.MultiHashMap(MultiHashMap)
import qualified Util.MultiHashMap as MultiHashMap

data VIXState = VIXState
  { vixLocation :: SourceLoc
  , vixContext :: HashMap QName (Definition Expr Void, Type Void)
  , vixModuleNames :: MultiHashMap ModuleName (Either QConstr QName)
  , vixConvertedSignatures :: HashMap QName Lifted.FunSignature
  , vixSignatures :: HashMap QName (Signature ReturnIndirect)
  , vixClassMethods :: HashMap QName (Vector Name)
  , vixClassInstances :: HashMap QName [(QName, Type Void)]
  , vixIndent :: !Int
  , vixFresh :: !Int
  , vixLogHandle :: !Handle
  , vixVerbosity :: !Int
  , vixTarget :: Target
  }

type MonadVIX = MonadState VIXState

emptyVIXState :: Target -> Handle -> Int -> VIXState
emptyVIXState target handle verbosity = VIXState
  { vixLocation = mempty
  , vixContext = mempty
  , vixModuleNames = mempty
  , vixConvertedSignatures = mempty
  , vixSignatures = mempty
  , vixClassMethods = mempty
  , vixClassInstances = mempty
  , vixIndent = 0
  , vixFresh = 0
  , vixLogHandle = handle
  , vixVerbosity = verbosity
  , vixTarget = target
  }

newtype VIX a = VIX (StateT VIXState (ExceptT String IO) a)
  deriving (Functor, Applicative, Monad, MonadFix, MonadError String, MonadState VIXState, MonadIO)

liftST :: MonadIO m => ST RealWorld a -> m a
liftST = liftIO . stToIO

unVIX
  :: VIX a
  -> StateT VIXState (ExceptT String IO) a
unVIX (VIX x) = x

-- TODO vixFresh should probably be a mutable variable
runVIX
  :: VIX a
  -> Target
  -> Handle
  -> Int
  -> IO (Either String a)
runVIX vix target handle verbosity
  = runExceptT
  $ evalStateT (unVIX vix)
  $ emptyVIXState target handle verbosity

fresh :: MonadVIX m => m Int
fresh = do
  i <- gets vixFresh
  modify $ \s -> s {vixFresh = i + 1}
  return i

located :: MonadVIX m => SourceLoc -> m a -> m a
located loc m = do
  oldLoc <- gets vixLocation
  modify $ \s -> s { vixLocation = loc }
  res <- m
  modify $ \s -> s { vixLocation = oldLoc }
  return res

currentLocation :: MonadVIX m => m SourceLoc
currentLocation = gets vixLocation

-------------------------------------------------------------------------------
-- Debugging
log :: (MonadIO m, MonadVIX m) => Text -> m ()
log l = do
  h <- gets vixLogHandle
  liftIO $ Text.hPutStrLn h l

logVerbose :: (MonadIO m, MonadVIX m) => Int -> Text -> m ()
logVerbose v l = whenVerbose v $ VIX.log l

modifyIndent :: (MonadIO m, MonadVIX m) => (Int -> Int) -> m ()
modifyIndent f = modify $ \s -> s {vixIndent = f $ vixIndent s}

logPretty :: (MonadIO m, MonadVIX m, Pretty a) => Int -> String -> a -> m ()
logPretty v s x = whenVerbose v $ do
  i <- gets vixIndent
  VIX.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide (pretty x)

logShow :: (MonadIO m, MonadVIX m, Show a) => Int -> String -> a -> m ()
logShow v s x = whenVerbose v $ do
  i <- gets vixIndent
  VIX.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> fromString (show x)

whenVerbose :: MonadVIX m => Int -> m () -> m ()
whenVerbose i m = do
  v <- gets vixVerbosity
  when (v >= i) m

-------------------------------------------------------------------------------
-- Working with abstract syntax
addContext :: MonadVIX m => HashMap QName (Definition Expr Void, Type Void) -> m ()
addContext prog = modify $ \s -> s
  { vixContext = prog <> vixContext s
  , vixClassInstances = HashMap.unionWith (<>) instances $ vixClassInstances s
  } where
    unions = foldl' (HashMap.unionWith (<>)) mempty
    instances
      = unions
      $ flip map (HashMap.toList prog) $ \(defName, (def, typ)) -> case def of
        DataDefinition {} -> mempty
        Definition _ IsOrdinaryDefinition _ -> mempty
        Definition _ IsInstance _ -> do
          let (_, s) = pisView typ
          case appsView $ fromScope s of
            (Global className, _) -> HashMap.singleton className [(defName, typ)]
            _ -> mempty


throwLocated
  :: (MonadError String m, MonadVIX m)
  => Doc
  -> m a
throwLocated x = do
  loc <- currentLocation
  throwError
    $ show
    $ explain loc
    $ Err (Just $ pretty x) mempty mempty mempty

definition
  :: (MonadVIX m, MonadError String m)
  => QName
  -> m (Definition Expr v, Expr v)
definition name = do
  mres <- gets $ HashMap.lookup name . vixContext
  maybe (throwLocated $ "Not in scope: " <> pretty name)
        (return . bimap vacuous vacuous)
        mres

addModule
  :: MonadVIX m
  => ModuleName
  -> HashSet (Either QConstr QName)
  -> m ()
addModule m names = modify $ \s -> s
  { vixModuleNames = MultiHashMap.inserts m names $ vixModuleNames s
  }

qconstructor :: (MonadVIX m, MonadError String m) => QConstr -> m (Type v)
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
  :: MonadVIX m
  => HashMap QName Lifted.FunSignature
  -> m ()
addConvertedSignatures p
  = modify $ \s -> s { vixConvertedSignatures = p <> vixConvertedSignatures s }

convertedSignature
  :: MonadVIX m
  => QName
  -> m (Maybe Lifted.FunSignature)
convertedSignature name = gets $ HashMap.lookup name . vixConvertedSignatures

addSignatures
  :: MonadVIX m
  => HashMap QName (Signature ReturnIndirect)
  -> m ()
addSignatures p = modify $ \s -> s { vixSignatures = p <> vixSignatures s }

signature
  :: (MonadError String m, MonadVIX m)
  => QName
  -> m (Signature ReturnIndirect)
signature name = do
  sigs <- gets vixSignatures
  mres <- gets $ HashMap.lookup name . vixSignatures
  maybe (throwError $ "Not in scope: signature for " ++ show name ++ show sigs)
        return
        mres

-------------------------------------------------------------------------------
-- General constructor queries
qconstructorIndex
  :: MonadVIX m
  => m (QConstr -> Maybe Int)
qconstructorIndex = do
  cxt <- gets vixContext
  return $ \(QConstr n c) -> do
    (DataDefinition (DataDef constrDefs) _, _) <- HashMap.lookup n cxt
    case constrDefs of
      [] -> Nothing
      [_] -> Nothing
      _ -> findIndex ((== c) . constrName) constrDefs

constrArity
  :: (MonadVIX m, MonadError String m)
  => QConstr
  -> m Int
constrArity
  = fmap (teleLength . fst . pisView)
  . qconstructor

constrIndex
  :: (MonadError String m, MonadVIX m)
  => QConstr
  -> m Int
constrIndex qc@(QConstr n c) = do
  (DataDefinition (DataDef cs) _, _) <- definition n
  case List.findIndex ((== c) . constrName) cs of
    Just i -> return i
    Nothing -> throwError $ "Can't find index for " ++ show qc
