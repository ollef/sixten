{-# LANGUAGE DefaultSignatures, FlexibleContexts, GADTs, GeneralizedNewtypeDeriving, OverloadedStrings, UndecidableInstances #-}
module VIX where

import Control.Monad.Base
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Trans.Control
import Control.Monad.Trans.Identity
import Control.Monad.Writer
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Lazy(HashMap)
import Data.HashSet(HashSet)
import Data.List as List
import Data.String
import Data.Text(Text)
import qualified Data.Text.IO as Text
import Data.Vector(Vector)
import Data.Void
import Data.Word
import qualified LLVM.IRBuilder as IRBuilder
import System.IO

import Backend.Target as Target
import Error
import Fresh
import Syntax
import Syntax.Abstract
import qualified Syntax.Sized.Lifted as Lifted
import TypeRep
import Util.MultiHashMap(MultiHashMap)
import qualified Util.MultiHashMap as MultiHashMap

data VIXState = VIXState
  { vixLocation :: Maybe SourceLoc
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

class MonadFresh m => MonadVIX m where
  liftVIX :: State VIXState a -> m a

  default liftVIX
    :: (MonadTrans t, MonadVIX m1, m ~ t m1)
    => State VIXState a
    -> m a
  liftVIX = lift . liftVIX

emptyVIXState :: Target -> Handle -> Int -> VIXState
emptyVIXState target handle verbosity = VIXState
  { vixLocation = Nothing
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

newtype VIX a = VIX (StateT VIXState (ExceptT Error IO) a)
  deriving (Functor, Applicative, Monad, MonadFix, MonadError Error, MonadIO, MonadBase IO, MonadBaseControl IO)

instance MonadVIX VIX where
  liftVIX (StateT s) = VIX $ StateT $ pure . runIdentity . s

liftST :: MonadIO m => ST RealWorld a -> m a
liftST = liftIO . stToIO

unVIX
  :: VIX a
  -> StateT VIXState (ExceptT Error IO) a
unVIX (VIX x) = x

-- TODO vixFresh should probably be a mutable variable
runVIX
  :: VIX a
  -> Target
  -> Handle
  -> Int
  -> IO (Either Error a)
runVIX vix target handle verbosity
  = runExceptT
  $ evalStateT (unVIX vix)
  $ emptyVIXState target handle verbosity

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
log :: (MonadIO m, MonadVIX m) => Text -> m ()
log l = do
  h <- liftVIX $ gets vixLogHandle
  liftIO $ Text.hPutStrLn h l

logVerbose :: (MonadIO m, MonadVIX m) => Int -> Text -> m ()
logVerbose v l = whenVerbose v $ VIX.log l

indentLog :: MonadVIX m => m a -> m a
indentLog m = do
  liftVIX $ modify $ \s -> s { vixIndent = vixIndent s + 1 }
  res <- m
  liftVIX $ modify $ \s -> s { vixIndent = vixIndent s - 1 }
  return res

logPretty :: (MonadIO m, MonadVIX m, Pretty a) => Int -> String -> a -> m ()
logPretty v s x = whenVerbose v $ do
  i <- liftVIX $ gets vixIndent
  VIX.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide (pretty x)

logShow :: (MonadIO m, MonadVIX m, Show a) => Int -> String -> a -> m ()
logShow v s x = whenVerbose v $ do
  i <- liftVIX $ gets vixIndent
  VIX.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> fromString (show x)

whenVerbose :: MonadVIX m => Int -> m () -> m ()
whenVerbose i m = do
  v <- liftVIX $ gets vixVerbosity
  when (v >= i) m

-------------------------------------------------------------------------------
-- Working with abstract syntax
addContext :: MonadVIX m => HashMap QName (Definition Expr Void, Type Void) -> m ()
addContext prog = liftVIX $ modify $ \s -> s
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
  -> m (Definition Expr v, Expr v)
definition name = do
  mres <- liftVIX $ gets $ HashMap.lookup name . vixContext
  maybe (throwLocated $ "Not in scope: " <> pretty name)
        (return . bimap vacuous vacuous)
        mres

addModule
  :: MonadVIX m
  => ModuleName
  -> HashSet (Either QConstr QName)
  -> m ()
addModule m names = liftVIX $ modify $ \s -> s
  { vixModuleNames = MultiHashMap.inserts m names $ vixModuleNames s
  }

qconstructor :: (MonadVIX m, MonadError Error m) => QConstr -> m (Type v)
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
  :: (MonadVIX m, MonadError Error m)
  => QConstr
  -> m (Maybe Int)
constrIndex (QConstr n c) = do
  mres <- liftVIX $ gets $ HashMap.lookup n . vixContext
  return $ case mres of
    Just (DataDefinition (DataDef constrDefs@(_:_:_)) _, _) ->
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
