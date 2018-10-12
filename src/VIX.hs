{-# LANGUAGE DefaultSignatures, FlexibleContexts, GADTs, GeneralizedNewtypeDeriving, OverloadedStrings, UndecidableInstances #-}
module VIX where

import Control.Monad.Base
import Control.Monad.Except
import Control.Monad.Fail
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Control
import Control.Monad.Writer
import Data.Foldable
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Lazy(HashMap)
import Data.HashSet(HashSet)
import Data.List as List
import Data.String
import qualified Data.Text.IO as Text
import Data.Word
import qualified LLVM.IRBuilder as IRBuilder
import System.IO

import Backend.Target as Target
import Error
import MonadFresh
import MonadLog
import Processor.Result
import Syntax
import Syntax.Core
import qualified Syntax.Sized.Lifted as Lifted
import TypedFreeVar
import TypeRep
import Util
import Util.MultiHashMap(MultiHashMap)
import qualified Util.MultiHashMap as MultiHashMap

data VIXState = VIXState
  { vixLocation :: Maybe SourceLoc
  , vixEnvironment :: HashMap QName (SourceLoc, ClosedDefinition Expr, Biclosed Type)
  , vixModuleConstrs :: MultiHashMap ModuleName QConstr
  , vixModuleNames :: MultiHashMap ModuleName QName
  , vixConvertedSignatures :: HashMap QName Lifted.FunSignature
  , vixSignatures :: HashMap QName (Signature ReturnIndirect)
  , vixClassMethods :: HashMap QName [(Name, SourceLoc)]
  , vixClassInstances :: MultiHashMap QName QName
  , vixIndent :: !Int
  , vixFresh :: !Int
  , vixLogHandle :: !Handle
  , vixVerbosity :: !Int
  , vixTarget :: Target
  , vixSilentErrors :: !Bool
  , vixErrors :: [Error]
  }

class MonadFresh m => MonadVIX m where
  liftVIX :: State VIXState a -> m a

  default liftVIX
    :: (MonadTrans t, MonadVIX m1, m ~ t m1)
    => State VIXState a
    -> m a
  liftVIX = lift . liftVIX

instance MonadReport VIX where
  report e = do
    silent <- liftVIX $ gets vixSilentErrors
    unless silent $ liftIO $ printError e
    liftVIX $ modify $ \s -> s { vixErrors = e : vixErrors s }

emptyVIXState :: Target -> Handle -> Int -> Bool -> VIXState
emptyVIXState target handle verbosity' silent = VIXState
  { vixLocation = Nothing
  , vixEnvironment = mempty
  , vixModuleConstrs = mempty
  , vixModuleNames = mempty
  , vixConvertedSignatures = mempty
  , vixSignatures = mempty
  , vixClassMethods = mempty
  , vixClassInstances = mempty
  , vixIndent = 0
  , vixFresh = 0
  , vixLogHandle = handle
  , vixVerbosity = verbosity'
  , vixTarget = target
  , vixSilentErrors = silent
  , vixErrors = mempty
  }

newtype VIX a = VIX { unVIX :: StateT VIXState (ExceptT Error IO) a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadFix, MonadError Error, MonadIO, MonadBase IO, MonadBaseControl IO)

instance MonadVIX VIX where
  liftVIX (StateT s) = VIX $ StateT $ pure . runIdentity . s

runVIX
  :: VIX a
  -> Target
  -> Handle
  -> Int
  -> Bool
  -> IO (Result (a, [Error]))
runVIX vix target handle verbosity' silent = do
  result <- runExceptT
    $ runStateT (unVIX vix)
    $ emptyVIXState target handle verbosity' silent
  return $ case result of
    Left err -> Failure [err]
    Right (a, s) -> pure (a, reverse $ vixErrors s)

instance MonadFresh VIX where
  fresh = liftVIX $ do
    i <- gets vixFresh
    modify $ \s -> s {vixFresh = i + 1}
    return i

located :: MonadVIX m => SourceLoc -> m a -> m a
located loc m = do
  oldLoc <- liftVIX $ gets vixLocation
  liftVIX $ modify $ \s -> s { vixLocation = Just loc }
  res <- m
  liftVIX $ modify $ \s -> s { vixLocation = oldLoc }
  return res

currentLocation :: MonadVIX m => m (Maybe SourceLoc)
currentLocation = liftVIX $ gets vixLocation

-------------------------------------------------------------------------------
-- Debugging
instance MonadLog VIX where
  log l = do
    h <- liftVIX $ gets vixLogHandle
    liftIO $ Text.hPutStrLn h l
  verbosity = liftVIX $ gets vixVerbosity

indentLog :: MonadVIX m => m a -> m a
indentLog m = do
  liftVIX $ modify $ \s -> s { vixIndent = vixIndent s + 1 }
  res <- m
  liftVIX $ modify $ \s -> s { vixIndent = vixIndent s - 1 }
  return res

logPretty :: (MonadLog m, MonadVIX m, Pretty a) => Int -> String -> a -> m ()
logPretty v s x = whenVerbose v $ do
  i <- liftVIX $ gets vixIndent
  MonadLog.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide (pretty x)

logShow :: (MonadLog m, MonadVIX m, Show a) => Int -> String -> a -> m ()
logShow v s x = whenVerbose v $ do
  i <- liftVIX $ gets vixIndent
  MonadLog.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> fromString (show x)

-- | Like freeVar, but with logging
forall
  :: (MonadFresh m, MonadVIX m, MonadLog m)
  => NameHint
  -> d
  -> e (FreeVar d e)
  -> m (FreeVar d e)
forall h p t = do
  v <- freeVar h p t
  logVerbose 20 $ "forall: " <> shower (varId v)
  return v

logFreeVar
  :: (Functor e, Functor f, Foldable f, Pretty (f Doc), Pretty (e Doc), MonadVIX m, MonadLog m)
  => Int
  -> String
  -> f (FreeVar d e)
  -> m ()
logFreeVar v s x = whenVerbose v $ do
  i <- liftVIX $ gets vixIndent
  let r = showFreeVar x
  MonadLog.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide r

-------------------------------------------------------------------------------
-- Working with abstract syntax
addEnvironment :: MonadVIX m => HashMap QName (SourceLoc, ClosedDefinition Expr, Biclosed Type) -> m ()
addEnvironment prog = liftVIX $ modify $ \s -> s
  { vixEnvironment = prog <> vixEnvironment s
  }

throwLocated
  :: (MonadError Error m, MonadVIX m)
  => Doc
  -> m a
throwLocated x = do
  loc <- currentLocation
  throwError $ TypeError x loc mempty

internalError :: MonadError Error m => Doc -> m a
internalError d = throwError $ InternalError d Nothing mempty

definition
  :: (MonadVIX m, MonadError Error m)
  => QName
  -> m (Definition (Expr meta) v, Expr meta v)
definition name = do
  mres <- liftVIX $ gets $ HashMap.lookup name . vixEnvironment
  maybe (throwLocated $ "Not in scope: " <> pretty name)
        (\(_, ClosedDefinition d, Biclosed t) -> pure (d, t))
        mres

instances
  :: MonadVIX m
  => QName
  -> m [(QName, Expr meta v)]
instances className = do
  instanceNames <- liftVIX $ gets $ MultiHashMap.lookup className . vixClassInstances
  fmap concat $ forM (toList instanceNames) $ \instanceName ->
    liftVIX
      $ gets
      $ maybe mempty (\(_, _, Biclosed t) -> pure (instanceName, t))
        . HashMap.lookup instanceName
        . vixEnvironment

addModule
  :: MonadVIX m
  => ModuleName
  -> HashSet QConstr
  -> HashSet QName
  -> m ()
addModule m constrs names = liftVIX $ modify $ \s -> s
  { vixModuleConstrs = MultiHashMap.inserts m constrs $ vixModuleConstrs s
  , vixModuleNames = MultiHashMap.inserts m names $ vixModuleNames s
  }

qconstructor :: (MonadVIX m, MonadError Error m) => QConstr -> m (Type meta v)
qconstructor qc@(QConstr n c) = do
  (def, _) <- definition n
  case def of
    DataDefinition ddef _ -> do
      let qcs = quantifiedConstrTypes ddef implicitise
      case filter ((== c) . constrName) qcs of
        [] -> throwLocated $ "Not in scope: constructor " <> pretty qc
        [cdef] -> return $ constrType cdef
        _ -> throwLocated $ "Ambiguous constructor: " <> pretty qc
    ConstantDefinition {} -> no
  where
    no = throwLocated $ "Not a data type: " <> pretty n

-------------------------------------------------------------------------------
-- Signatures
addConvertedSignatures
  :: MonadVIX m
  => HashMap QName Lifted.FunSignature
  -> m ()
addConvertedSignatures p
  = liftVIX
  $ modify $ \s -> s { vixConvertedSignatures = p <> vixConvertedSignatures s }

convertedSignature
  :: MonadVIX m
  => QName
  -> m (Maybe Lifted.FunSignature)
convertedSignature name = liftVIX $ gets $ HashMap.lookup name . vixConvertedSignatures

addSignatures
  :: MonadVIX m
  => HashMap QName (Signature ReturnIndirect)
  -> m ()
addSignatures p = liftVIX $ modify $ \s -> s { vixSignatures = p <> vixSignatures s }

signature
  :: MonadVIX m
  => QName
  -> m (Maybe (Signature ReturnIndirect))
signature name = liftVIX $ gets $ HashMap.lookup name . vixSignatures

-------------------------------------------------------------------------------
-- General constructor queries
constrArity
  :: (MonadVIX m, MonadError Error m)
  => QConstr
  -> m Int
constrArity
  = fmap (teleLength . fst . pisView)
  . qconstructor

constrIndex
  :: MonadVIX m
  => QConstr
  -> m (Maybe Int)
constrIndex (QConstr n c) = do
  mres <- liftVIX $ gets $ HashMap.lookup n . vixEnvironment
  return $ case mres of
    Just (_, ClosedDefinition (DataDefinition (DataDef _ constrDefs@(_:_:_)) _), _) ->
      findIndex ((== c) . constrName) constrDefs
    _ -> Nothing

-------------------------------------------------------------------------------
-- Type representation queries
getIntRep :: MonadVIX m => m TypeRep
getIntRep = TypeRep.intRep <$> getTarget

getPtrRep :: MonadVIX m => m TypeRep
getPtrRep = TypeRep.ptrRep <$> getTarget

getTypeRep :: MonadVIX m => m TypeRep
getTypeRep = TypeRep.typeRep <$> getTarget

getPiRep :: MonadVIX m => m TypeRep
getPiRep = TypeRep.piRep <$> getTarget

getIntBits :: MonadVIX m => m Word32
getIntBits = Target.intBits <$> getTarget

getTypeRepBits :: MonadVIX m => m Word32
getTypeRepBits = (* Target.byteBits) . fromIntegral . TypeRep.size <$> getTypeRep

getPtrAlign :: MonadVIX m => m Word32
getPtrAlign = Target.ptrAlign <$> getTarget

getTarget :: MonadVIX m => m Target
getTarget = liftVIX $ gets vixTarget

-------------------------------------------------------------------------------
-- mtl instances
-------------------------------------------------------------------------------
instance MonadVIX m => MonadVIX (ReaderT r m)
instance (Monoid w, MonadVIX m) => MonadVIX (WriterT w m)
instance MonadVIX m => MonadVIX (StateT s m)
instance MonadVIX m => MonadVIX (IdentityT m)
instance MonadVIX m => MonadVIX (IRBuilder.IRBuilderT m)
instance MonadVIX m => MonadVIX (IRBuilder.ModuleBuilderT m)
instance MonadVIX m => MonadVIX (ExceptT e m)
