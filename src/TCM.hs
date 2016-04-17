{-# LANGUAGE GeneralizedNewtypeDeriving, Rank2Types, TypeFamilies #-}
module TCM where

import Control.Monad.Except
import Control.Monad.State(MonadState, evalStateT, StateT, runStateT, gets, modify)
import Control.Monad.ST
import Control.Monad.ST.Class
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HM
import Data.HashMap.Lazy(HashMap)
import Data.Monoid
import Data.Set(Set)
import qualified Data.Set as Set
import qualified Data.Vector as Vector
import Data.Void

import Syntax
import Syntax.Abstract

import Debug.Trace

newtype Level = Level Int
  deriving (Eq, Num, Ord, Show)

instance Pretty Level where
  pretty (Level i) = pretty i

data State = State
  { tcContext :: Program Expr Void
  , tcArities :: HashMap Name Int
  , tcConstrs :: HashMap Constr (Set (Name, Type Void))
  , tcIndent  :: !Int -- This has no place here, but is useful for debugging
  , tcFresh   :: !Int
  , tcLevel   :: !Level
  , tcLog     :: ![String]
  }

instance Monoid State where
  mempty = State
    { tcContext = mempty
    , tcConstrs = mempty
    , tcArities = mempty
    , tcIndent  = 0
    , tcFresh   = 0
    , tcLevel   = Level 1
    , tcLog     = mempty
    }
  mappend (State cxt1 cs1 as1 x1 y1 z1 l1) (State cxt2 cs2 as2 x2 y2 z2 l2)
    = State (cxt1 <> cxt2) (cs1 <> cs2) (as1 <> as2) (x1 + x2) (y1 + y2) (z1 + z2) (l1 <> l2)

newtype TCM s a = TCM (ExceptT String (StateT State (ST s)) a)
  deriving (Functor, Applicative, Monad, MonadFix, MonadError String, MonadState State)

instance MonadST (TCM s) where
  type World (TCM s) = s
  liftST = TCM . liftST

unTCM :: (forall s. TCM s a) -> forall s. ExceptT String (StateT State (ST s)) a
unTCM (TCM x) = x

evalTCM :: (forall s. TCM s a) -> Program Expr Void -> Either String a
evalTCM tcm cxt = runST $ evalStateT (runExceptT $ unTCM tcm) mempty { tcContext = cxt }

runTCM :: (forall s. TCM s a) -> Program Expr Void -> (Either String a, [String])
runTCM tcm cxt = second (reverse . tcLog) $ runST $ runStateT (runExceptT $ unTCM tcm) mempty { tcContext = cxt }

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

log :: String -> TCM s ()
log l = trace l $ modify $ \s -> s {tcLog = l : tcLog s}

addContext :: Program Expr Void -> TCM s ()
addContext prog = modify $ \s -> s
  { tcContext = prog <> tcContext s
  , tcConstrs = HM.unionWith (<>) cs $ tcConstrs s
  , tcArities = arities <> tcArities s
  } where
    arities = HM.fromList $ do
      (n, (def, defType)) <- HM.toList prog
      return
        ( n
        , Vector.length
        $ Vector.filter (\(_, a, _) -> relevance a == Relevant)
        $ unTelescope $ fst
        $ case def of
            Definition e -> bindingsView lamView e
            DataDefinition _ -> bindingsView piView defType
        )

    cs = HM.fromList $ do
      (n, (DataDefinition d, defType)) <- HM.toList prog
      ConstrDef c t <- quantifiedConstrTypes
                         (\h _p -> Syntax.pi_ h IrIm)
                         d
                         (telescope defType)
      return (c, Set.fromList [(n, t)])

addArity :: Name -> Int -> TCM s ()
addArity n arity = modify $ \s -> s { tcArities = HM.insert n arity $ tcArities s }

modifyIndent :: (Int -> Int) -> TCM s ()
modifyIndent f = modify $ \s -> s {tcIndent = f $ tcIndent s}

lookupDefinition :: Name -> TCM s (Maybe (Definition Expr b, Type b'))
lookupDefinition name = gets $ fmap (bimap vacuous vacuous) . HM.lookup name . tcContext
lookupConstructor :: Ord b => Constr -> TCM s (Set (Name, Type b))
lookupConstructor name = gets $ maybe mempty (Set.map $ second vacuous) . HM.lookup name . tcConstrs

definition
  :: Name
  -> TCM s (Definition Expr v, Type v)
definition v = do
  mres <- lookupDefinition v
  maybe (throwError $ "Not in scope: " ++ show v)
        (return . bimap vacuous vacuous)
        mres

constructor
  :: Ord v
  => Either Constr QConstr
  -> TCM s (Set (Name, Type v))
constructor (Right qc@(QConstr n _)) = Set.singleton . (,) n <$> qconstructor qc
constructor (Left c) = Set.map (second vacuous) <$> lookupConstructor c

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

relevantDefArity
  :: Name
  -> TCM s Int
relevantDefArity n = do
  mres <- gets (HM.lookup n . tcArities)
  maybe (throwError $ "Not in scope: " ++ show n)
        return
        mres

constrArity
  :: QConstr
  -> TCM s Int
constrArity = fmap (teleLength . fst . bindingsView piView) . qconstructor

relevantConstrArity
  :: QConstr
  -> TCM s Int
relevantConstrArity
  = fmap ( Vector.length
         . Vector.filter (\(_, a, _) -> relevance a == Relevant)
         . unTelescope
         . fst
         . bindingsView piView)
  . qconstructor
