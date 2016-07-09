{-# LANGUAGE GeneralizedNewtypeDeriving, Rank2Types, TypeFamilies #-}
module TCM where

import Control.Monad.Except
import Control.Monad.State(MonadState, evalStateT, StateT, runStateT, gets, modify)
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
import qualified Data.Vector as Vector
import Data.Void

import Syntax
import Syntax.Abstract
import qualified Syntax.Converted as Converted
import qualified Syntax.Restricted as Restricted
import Util

import Debug.Trace

newtype Level = Level Int
  deriving (Eq, Num, Ord, Show)

instance Pretty Level where
  pretty (Level i) = pretty i

data State = State
  { tcContext :: Program Expr Void
  , tcConstrs :: HashMap Constr (Set (Name, Type Void))
  , tcConvertedSignatures :: HashMap Name (Converted.Signature Unit Void)
  , tcRestrictedContext :: HashMap Name (Restricted.Body Void)
  , tcIndent :: !Int -- This has no place here, but is useful for debugging
  , tcFresh :: !Int
  , tcLevel :: !Level
  , tcLog :: ![Doc]
  }

emptyState :: State
emptyState = State
  { tcContext = mempty
  , tcConstrs = mempty
  , tcConvertedSignatures = mempty
  , tcRestrictedContext = mempty
  , tcIndent = 0
  , tcFresh = 0
  , tcLevel = Level 1
  , tcLog = mempty
  }

newtype TCM s a = TCM (ExceptT String (StateT State (ST s)) a)
  deriving (Functor, Applicative, Monad, MonadFix, MonadError String, MonadState State)

instance MonadST (TCM s) where
  type World (TCM s) = s
  liftST = TCM . liftST

unTCM
  :: (forall s. TCM s a)
  -> forall s. ExceptT String (StateT State (ST s)) a
unTCM (TCM x) = x

evalTCM
  :: (forall s. TCM s a)
  -> Program Expr Void
  -> Either String a
evalTCM tcm cxt
  = runST
  $ evalStateT (runExceptT $ unTCM tcm)
               emptyState { tcContext = cxt }

runTCM
  :: (forall s. TCM s a)
  -> Program Expr Void
  -> (Either String a, [Doc])
runTCM tcm cxt
  = second (reverse . tcLog)
  $ runST
  $ runStateT (runExceptT $ unTCM tcm)
              emptyState { tcContext = cxt }

fresh :: TCM s Int
fresh = do
  i <- gets tcFresh
  modify $ \s -> s {tcFresh = i + 1}
  return i

level :: TCM s Level
level = gets tcLevel

enterLevel :: TCM s a -> TCM s a
enterLevel x = do
  l <- level
  modify $ \s -> s {tcLevel = l + 1}
  r <- x
  modify $ \s -> s {tcLevel = l}
  return r

log :: Lazy.Text -> TCM s ()
log l = trace (Lazy.unpack l) $ modify $ \s -> s {tcLog = text l : tcLog s}

addContext :: Program Expr Void -> TCM s ()
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
  :: HashMap Name (Converted.Signature a b)
  -> TCM s ()
addConvertedSignatures p = modify $ \s -> s { tcConvertedSignatures = p' <> tcConvertedSignatures s }
  where
    p' = fmap (const $ error "addConvertedSignatures")
       . Converted.mapSignature (const Unit) <$> p

addRestrictedContext
  :: HashMap Name (Restricted.Body Void)
  -> TCM s ()
addRestrictedContext p = modify $ \s -> s { tcRestrictedContext = p <> tcRestrictedContext s}

modifyIndent :: (Int -> Int) -> TCM s ()
modifyIndent f = modify $ \s -> s {tcIndent = f $ tcIndent s}

lookupDefinition
  :: Name
  -> TCM s (Maybe (Definition Expr b, Type b'))
lookupDefinition name
  = gets
  $ fmap (bimap vacuous vacuous)
  . HM.lookup name
  . tcContext

lookupConstructor
  :: Ord b
  => Constr
  -> TCM s (Set (Name, Type b))
lookupConstructor name
  = gets
  $ maybe mempty (Set.map $ second vacuous)
  . HM.lookup name
  . tcConstrs

lookupConvertedSignature
  :: Name
  -> TCM s (Maybe (Converted.Signature Unit Void))
lookupConvertedSignature name
  = gets
  $ HM.lookup name
  . tcConvertedSignatures

definition
  :: Name
  -> TCM s (Definition Expr v, Type v)
definition v = do
  mres <- lookupDefinition v
  maybe (throwError $ "Not in scope: " ++ show v)
        return
        mres

convertedSignature
  :: Name
  -> TCM s (Converted.Signature Unit Void)
convertedSignature v = do
  mres <- lookupConvertedSignature v
  maybe (throwError $ "Not in scope: converted " ++ show v)
        return
        mres

constructor
  :: Ord v
  => Either Constr QConstr
  -> TCM s (Set (Name, Type v))
constructor (Right qc@(QConstr n _)) = Set.singleton . (,) n <$> qconstructor qc
constructor (Left c) = lookupConstructor c

qconstructor
  :: QConstr
  -> TCM s (Type v)
qconstructor qc@(QConstr n c) = do
  results <- lookupConstructor c
  let filtered = Set.filter ((== n) . fst) results
  case Set.size filtered of
    1 -> do
      let [(_, t)] = Set.toList filtered
      return (vacuous t)
    0 -> throwError $ "Not in scope: constructor " ++ show qc
    _ -> throwError $ "Ambiguous constructor: " ++ show qc

qconstructorIndex :: TCM s (QConstr -> Maybe Int)
qconstructorIndex = do
  cxt <- gets tcContext
  return $ \(QConstr n c) -> do
    (DataDefinition (DataDef constrDefs), _) <- HM.lookup n cxt
    if length constrDefs == 1
    then Nothing
    else findIndex ((== c) . constrName) constrDefs

constrArity
  :: QConstr
  -> TCM s Int
constrArity = fmap (teleLength . fst . pisView) . qconstructor

constrIndex
  :: QConstr
  -> TCM s Int
constrIndex qc@(QConstr n c) = do
  (DataDefinition (DataDef cs), _) <- definition n
  case List.findIndex ((== c) . constrName) cs of
    Just i -> return i
    Nothing -> throwError $ "Can't find index for " ++ show qc

relevantConstrArity
  :: QConstr
  -> TCM s Int
relevantConstrArity
  = fmap ( Vector.length
         . Vector.filter (\(_, a, _) -> relevance a == Relevant)
         . unTelescope
         . fst
         . pisView)
  . qconstructor
