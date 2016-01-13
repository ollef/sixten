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

import Syntax
import Syntax.Abstract
import Util

import Debug.Trace

newtype Level = Level Int
  deriving (Eq, Num, Ord, Show)

instance Pretty Level where
  pretty (Level i) = pretty i

data State = State
  { tcContext :: Program Annotation (Expr Annotation) Empty
  , tcConstrs :: HashMap Constr (Set (Name, Type Annotation Empty))
  , tcIndent  :: !Int -- This has no place here, but is useful for debugging
  , tcFresh   :: !Int
  , tcLevel   :: !Level
  , tcLog     :: ![String]
  }

instance Monoid State where
  mempty = State
    { tcContext = mempty
    , tcConstrs = mempty
    , tcIndent  = 0
    , tcFresh   = 0
    , tcLevel   = Level 1
    , tcLog     = mempty
    }
  mappend (State cxt1 cs1 x1 y1 z1 l1) (State cxt2 cs2 x2 y2 z2 l2)
    = State (cxt1 <> cxt2) (cs1 <> cs2) (x1 + x2) (y1 + y2) (z1 + z2) (l1 <> l2)

newtype TCM s a = TCM (ExceptT String (StateT State (ST s)) a)
  deriving (Functor, Applicative, Monad, MonadFix, MonadError String, MonadState State)

instance MonadST (TCM s) where
  type World (TCM s) = s
  liftST = TCM . liftST

unTCM :: (forall s. TCM s a) -> forall s. ExceptT String (StateT State (ST s)) a
unTCM (TCM x) = x

evalTCM :: (forall s. TCM s a) -> Program Annotation (Expr Annotation) Empty -> Either String a
evalTCM tcm cxt = runST $ evalStateT (runExceptT $ unTCM tcm) mempty { tcContext = cxt }

runTCM :: (forall s. TCM s a) -> Program Annotation (Expr Annotation) Empty -> (Either String a, [String])
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

addContext :: Program Annotation (Expr Annotation) Empty -> TCM s ()
addContext prog = modify $ \s -> s
  { tcContext = prog <> tcContext s
  , tcConstrs = HM.unionWith (<>) cs $ tcConstrs s
  } where
    cs = HM.fromList $ do
      (n, (DataDefinition d, defType, _)) <- HM.toList prog
      ConstrDef c t <- quantifiedConstrTypes
                         (\h p -> Pi h (Annotation (relevance p) Implicit))
                         d
                         (telescope defType)
      return (c, Set.fromList [(n, t)])

context :: Name -> TCM s (Definition (Expr Annotation) v, Type Annotation v, Annotation)
context v = do
  mres <- gets $ HM.lookup v . tcContext
  maybe (throwError $ "Not in scope: " ++ show v)
        (\(d, t, a) -> return (fromEmpty <$> d, fromEmpty <$> t, a))
        mres

constructor :: Ord v => Either Constr QConstr -> TCM s (Set (Name, Type Annotation v))
constructor (Right qc@(QConstr n _)) = do
  t <- qconstructor qc
  return $ Set.singleton (n, t)
constructor (Left c) = do
  mres <- gets $ HM.lookup c . tcConstrs
  maybe (throwError $ "Not in scope: constructor " ++ show c)
        (return . Set.map (second $ fmap fromEmpty))
        mres

qconstructor :: QConstr -> TCM s (Type Annotation v)
qconstructor qc@(QConstr n c) = do
  mres <- gets $ HM.lookup c . tcConstrs
  maybe (throwError $ "Not in scope: constructor " ++ show c)
        (\results -> do
          let filtered = Set.filter ((== n) . fst) results
          if Set.size filtered == 1 then do
            let [(_, t)] = Set.toList filtered
            return (fromEmpty <$> t)
          else
            throwError $ "Ambiguous constructor: " ++ show qc)
        mres

modifyIndent :: (Int -> Int) -> TCM s ()
modifyIndent f = modify $ \s -> s {tcIndent = f $ tcIndent s}

{-

conType :: ECon -> TCM s (Type k t)
conType c = do
  res <- M.lookup c <$> gets tcTypes
  maybe err (return . fromJust . biClosed) res
  where err = throwError $ "Not in scope: " ++ show c

tconKind :: TCon -> TCM s (Kind k)
tconKind a = do
  res <- M.lookup a <$> gets tcKinds
  maybe err (return . fromJust . closed) res
  where err = throwError $ "Not in scope: " ++ show a

synonym :: TCon -> TCM s (Type k t)
synonym a = do
  res <- M.lookup a <$> gets tcSynonyms
  return $ maybe (Type.Con a) (fromJust . biClosed) res
-}

whenM :: Monad m => m Bool -> m () -> m ()
whenM mb x = do b <- mb; when b x
