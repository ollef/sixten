{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, Rank2Types, TypeFamilies, OverloadedStrings #-}
module TCM where

import Control.Monad.Except
import Control.Monad.ST
import Control.Monad.ST.Class
import Control.Monad.State
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Lazy(HashMap)
import Data.List as List
import Data.Monoid
import Data.Set(Set)
import qualified Data.Set as Set
import Data.String
import Data.Text(Text)
import qualified Data.Text.IO as Text
import Data.Void
import System.IO

import Backend.Target
import Syntax
import Syntax.Abstract
import qualified Syntax.Sized.Closed as Closed

newtype Level = Level Int
  deriving (Eq, Num, Ord, Show)

instance Pretty Level where
  pretty (Level i) = pretty i

data TCMState = TCMState
  { tcLocation :: SourceLoc
  , tcContext :: HashMap Name (Definition Expr Void, Type Void)
  , tcConstrs :: HashMap Constr (Set (Name, Type Void))
  , tcConvertedSignatures :: HashMap Name Closed.FunSignature
  , tcSignatures :: HashMap Name (Signature ReturnIndirect)
  , tcIndent :: !Int
  , tcFresh :: !Int
  , tcLevel :: !Level
  , tcLogHandle :: !Handle
  , tcVerbosity :: !Int
  , tcTarget :: Target
  }

emptyTCMState :: Target -> Handle -> Int -> TCMState
emptyTCMState target handle verbosity = TCMState
  { tcLocation = mempty
  , tcContext = mempty
  , tcConstrs = mempty
  , tcConvertedSignatures = mempty
  , tcSignatures = mempty
  , tcIndent = 0
  , tcFresh = 0
  , tcLevel = Level 1
  , tcLogHandle = handle
  , tcVerbosity = verbosity
  , tcTarget = target
  }

newtype TCM a = TCM (ExceptT String (StateT TCMState IO) a)
  deriving (Functor, Applicative, Monad, MonadFix, MonadError String, MonadState TCMState, MonadIO)

instance MonadST TCM where
  type World TCM = RealWorld
  liftST = TCM . liftST

unTCM
  :: TCM a
  -> ExceptT String (StateT TCMState IO) a
unTCM (TCM x) = x

runTCM
  :: TCM a
  -> Target
  -> Handle
  -> Int
  -> IO (Either String a)
runTCM tcm target handle verbosity
  = evalStateT (runExceptT $ unTCM tcm)
  $ emptyTCMState target handle verbosity

fresh :: TCM Int
fresh = do
  i <- gets tcFresh
  modify $ \s -> s {tcFresh = i + 1}
  return i

level :: TCM Level
level = gets tcLevel

enterLevel :: TCM a -> TCM a
enterLevel x = do
  l <- level
  modify $ \s -> s {tcLevel = l + 1}
  r <- x
  modify $ \s -> s {tcLevel = l}
  return r

located :: SourceLoc -> TCM a -> TCM a
located loc m = do
  oldLoc <- gets tcLocation
  modify $ \s -> s { tcLocation = loc }
  res <- m
  modify $ \s -> s { tcLocation = oldLoc }
  return res

currentLocation :: TCM SourceLoc
currentLocation = gets tcLocation

-------------------------------------------------------------------------------
-- Debugging
log :: Text -> TCM ()
log l = do
  h <- gets tcLogHandle
  liftIO $ Text.hPutStrLn h l

logVerbose :: Int -> Text -> TCM ()
logVerbose v l = whenVerbose v $ TCM.log l

modifyIndent :: (Int -> Int) -> TCM ()
modifyIndent f = modify $ \s -> s {tcIndent = f $ tcIndent s}

logPretty :: Pretty a => Int -> String -> a -> TCM ()
logPretty v s x = whenVerbose v $ do
  i <- gets tcIndent
  TCM.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide (pretty x)

logShow :: Show a => Int -> String -> a -> TCM ()
logShow v s x = whenVerbose v $ do
  i <- gets tcIndent
  TCM.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> fromString (show x)

whenVerbose :: Int -> TCM () -> TCM ()
whenVerbose i m = do
  v <- gets tcVerbosity
  when (v >= i) m

-------------------------------------------------------------------------------
-- Working with abstract syntax
addContext :: HashMap Name (Definition Expr Void, Type Void) -> TCM ()
addContext prog = modify $ \s -> s
  { tcContext = prog <> tcContext s
  , tcConstrs = HashMap.unionWith (<>) cs $ tcConstrs s
  } where
    cs = HashMap.fromList $ do
      (n, (DataDefinition d _, defType)) <- HashMap.toList prog
      ConstrDef c t <- quantifiedConstrTypes d defType $ const Implicit
      return (c, Set.fromList [(n, t)])

definition :: Name -> TCM (Definition Expr v, Expr v)
definition name = do
  mres <- gets $ HashMap.lookup name . tcContext
  maybe (throwError $ "Not in scope: " ++ show name)
        (return . bimap vacuous vacuous)
        mres

qconstructor :: QConstr -> TCM (Expr v)
qconstructor qc@(QConstr n c) = do
  (def, typ) <- definition n
  case def of
    DataDefinition dataDef _ -> do
      let qcs = quantifiedConstrTypes dataDef typ $ const Implicit
      case filter ((== c) . constrName) qcs of
        [] -> throwError $ "Not in scope: constructor " ++ show qc
        [cdef] -> return $ constrType cdef
        _ -> throwError $ "Ambiguous constructor: " ++ show qc
    Definition _ -> throwError $ "Not a data type: " ++ show n

constructor
  :: Ord v
  => Either Constr QConstr
  -> TCM (Set (Name, Type v))
constructor (Right qc@(QConstr n _)) = Set.singleton . (,) n <$> qconstructor qc
constructor (Left c)
  = gets
  $ maybe mempty (Set.map $ second vacuous)
  . HashMap.lookup c
  . tcConstrs

-------------------------------------------------------------------------------
-- Signatures
addConvertedSignatures
  :: HashMap Name Closed.FunSignature
  -> TCM ()
addConvertedSignatures p
  = modify $ \s -> s { tcConvertedSignatures = p <> tcConvertedSignatures s }

convertedSignature
  :: Name
  -> TCM (Maybe Closed.FunSignature)
convertedSignature name = gets $ HashMap.lookup name . tcConvertedSignatures

addSignatures
  :: HashMap Name (Signature ReturnIndirect)
  -> TCM ()
addSignatures p = modify $ \s -> s { tcSignatures = p <> tcSignatures s }

signature
  :: Name
  -> TCM (Signature ReturnIndirect)
signature name = do
  mres <- gets $ HashMap.lookup name . tcSignatures
  maybe (throwError $ "Not in scope: signature for " ++ show name)
        return
        mres

-------------------------------------------------------------------------------
-- General constructor queries
qconstructorIndex :: TCM (QConstr -> Maybe Int)
qconstructorIndex = do
  cxt <- gets tcContext
  return $ \(QConstr n c) -> do
    (DataDefinition (DataDef constrDefs) _, _) <- HashMap.lookup n cxt
    case constrDefs of
      [] -> Nothing
      [_] -> Nothing
      _ -> findIndex ((== c) . constrName) constrDefs

constrArity
  :: QConstr
  -> TCM Int
constrArity
  = fmap (teleLength . fst . pisView)
  . (qconstructor :: QConstr -> TCM (Expr Void))

constrIndex
  :: QConstr
  -> TCM Int
constrIndex qc@(QConstr n c) = do
  (DataDefinition (DataDef cs) _, _) <- definition n
  case List.findIndex ((== c) . constrName) cs of
    Just i -> return i
    Nothing -> throwError $ "Can't find index for " ++ show qc
