{-# LANGUAGE GeneralizedNewtypeDeriving, Rank2Types, TypeFamilies #-}
module TCM where

import Control.Monad.Except
import Control.Monad.State(MonadState, evalStateT, StateT, gets, modify)
import Control.Monad.ST
import Control.Monad.ST.Class
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HM
import Data.HashMap.Lazy(HashMap)
import Data.List as List
import Data.Monoid
import Data.Set(Set)
import qualified Data.Set as Set
import qualified Data.Text.Lazy as Lazy
import qualified Data.Text.Lazy.IO as Lazy
import qualified Data.Vector as Vector
import Data.Void
import System.IO

import Syntax
import Syntax.Abstract
import qualified Syntax.Converted as Converted
import Util

newtype Level = Level Int
  deriving (Eq, Num, Ord, Show)

instance Pretty Level where
  pretty (Level i) = pretty i

data State = State
  { tcContext :: Program Expr Void
  , tcConstrs :: HashMap Constr (Set (Name, Type Void))
  , tcConvertedSignatures :: HashMap Name (Converted.Signature Converted.Expr Unit Void)
  , tcIndent :: !Int -- This has no place here, but is useful for debugging
  , tcFresh :: !Int
  , tcLevel :: !Level
  , tcLogHandle :: !Handle
  }

emptyState :: Handle -> State
emptyState handle = State
  { tcContext = mempty
  , tcConstrs = mempty
  , tcConvertedSignatures = mempty
  , tcIndent = 0
  , tcFresh = 0
  , tcLevel = Level 1
  , tcLogHandle = handle
  }

newtype TCM a = TCM (ExceptT String (StateT State IO) a)
  deriving (Functor, Applicative, Monad, MonadFix, MonadError String, MonadState State, MonadIO)

instance MonadST TCM where
  type World TCM = RealWorld
  liftST = TCM . liftST

unTCM
  :: TCM a
  -> ExceptT String (StateT State IO) a
unTCM (TCM x) = x

evalTCM
  :: TCM a
  -> Program Expr Void
  -> Handle
  -> IO (Either String a)
evalTCM tcm cxt handle
  = evalStateT (runExceptT $ unTCM tcm)
               (emptyState handle) { tcContext = cxt }

runTCM
  :: TCM a
  -> Program Expr Void
  -> Handle
  -> IO (Either String a)
runTCM tcm cxt handle
  = evalStateT (runExceptT $ unTCM tcm)
               (emptyState handle) { tcContext = cxt }

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

-- TODO
log :: Lazy.Text -> TCM ()
log l = do
  h <- gets tcLogHandle
  liftIO $ Lazy.hPutStrLn h l

addContext :: Program Expr Void -> TCM ()
addContext prog = modify $ \s -> s
  { tcContext = prog <> tcContext s
  , tcConstrs = HM.unionWith (<>) cs $ tcConstrs s
  }
  where
    cs = HM.fromList $ do
      (n, (DataDefinition d, defType)) <- HM.toList prog
      ConstrDef c t <- quantifiedConstrTypes
                         d
                         (mapAnnotations (const IrIm) $ telescope defType)
      return (c, Set.fromList [(n, t)])

addConvertedSignatures
  :: HashMap Name (Converted.Signature Converted.Expr b c)
  -> TCM ()
addConvertedSignatures p = modify $ \s -> s { tcConvertedSignatures = p' <> tcConvertedSignatures s }
  where
    p' = fmap (const $ error "addConvertedSignatures")
       . Converted.hoistSignature (const Unit) <$> p

modifyIndent :: (Int -> Int) -> TCM ()
modifyIndent f = modify $ \s -> s {tcIndent = f $ tcIndent s}

lookupDefinition
  :: Name
  -> TCM (Maybe (Definition Expr b, Type b'))
lookupDefinition name
  = gets
  $ fmap (bimap vacuous vacuous)
  . HM.lookup name
  . tcContext

lookupConstructor
  :: Ord b
  => Constr
  -> TCM (Set (Name, Type b))
lookupConstructor name
  = gets
  $ maybe mempty (Set.map $ second vacuous)
  . HM.lookup name
  . tcConstrs

lookupConvertedSignature
  :: Name
  -> TCM (Maybe (Converted.Signature Converted.Expr Unit Void))
lookupConvertedSignature name
  = gets
  $ HM.lookup name
  . tcConvertedSignatures

definition
  :: Name
  -> TCM (Definition Expr v, Type v)
definition v = do
  mres <- lookupDefinition v
  maybe (throwError $ "Not in scope: " ++ show v)
        return
        mres

convertedSignature
  :: Name
  -> TCM (Converted.Signature Converted.Expr Unit Void)
convertedSignature v = do
  mres <- lookupConvertedSignature v
  maybe (throwError $ "Not in scope: converted " ++ show v)
        return
        mres

constructor
  :: Ord v
  => Either Constr QConstr
  -> TCM (Set (Name, Type v))
constructor (Right qc@(QConstr n _)) = Set.singleton . (,) n <$> qconstructor qc
constructor (Left c) = lookupConstructor c

qconstructor
  :: QConstr
  -> TCM (Type v)
qconstructor qc@(QConstr n c) = do
  results <- lookupConstructor c
  let filtered = Set.filter ((== n) . fst) results
  case Set.size filtered of
    1 -> do
      let [(_, t)] = Set.toList filtered
      return (vacuous t)
    0 -> throwError $ "Not in scope: constructor " ++ show qc
    _ -> throwError $ "Ambiguous constructor: " ++ show qc

qconstructorIndex :: TCM (QConstr -> Maybe Int)
qconstructorIndex = do
  cxt <- gets tcContext
  return $ \(QConstr n c) -> do
    (DataDefinition (DataDef constrDefs), _) <- HM.lookup n cxt
    if length constrDefs == 1
    then Nothing
    else findIndex ((== c) . constrName) constrDefs

constrArity
  :: QConstr
  -> TCM Int
constrArity = fmap (teleLength . fst . pisView) . qconstructor

constrIndex
  :: QConstr
  -> TCM Int
constrIndex qc@(QConstr n c) = do
  (DataDefinition (DataDef cs), _) <- definition n
  case List.findIndex ((== c) . constrName) cs of
    Just i -> return i
    Nothing -> throwError $ "Can't find index for " ++ show qc

relevantConstrArity
  :: QConstr
  -> TCM Int
relevantConstrArity
  = fmap ( Vector.length
         . Vector.filter (\(_, a, _) -> relevance a == Relevant)
         . unTelescope
         . fst
         . pisView)
  . qconstructor
