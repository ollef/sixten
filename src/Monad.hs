{-# LANGUAGE RankNTypes #-}
module Monad where

import Control.Monad.Except
import Control.Monad.State(evalStateT, StateT, runStateT, gets, modify)
import Control.Monad.ST
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HM
import Data.HashMap.Lazy(HashMap)
import Data.Monoid
import Data.Set(Set)
import qualified Data.Set as Set

import Syntax
import Syntax.Abstract
import Util

newtype Level = Level Int
  deriving (Eq, Ord, Show)

instance Pretty Level where
  pretty (Level i) = pretty i

data State = State
  { tcContext :: Program (Expr Annotation) Annotation Empty
  , tcConstrs :: HashMap Constr (Set (Name, Type Annotation Empty))
  , tcIndent  :: {-# UNPACK #-} !Int -- This has no place here, but is useful for debugging
  , tcFresh   :: {-# UNPACK #-} !Int
  , tcLevel   :: {-# UNPACK #-} !Level
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
    where
  mappend (State cxt1 cs1 x1 y1 (Level z1) l1) (State cxt2 cs2 x2 y2 (Level z2) l2)
    = State (cxt1 <> cxt2) (cs1 <> cs2) (x1 + x2) (y1 + y2) (Level $ z1 + z2) (l1 <> l2)

type TCM s = ExceptT String (StateT State (ST s))

evalTCM :: (forall s. TCM s a) -> Either String a
evalTCM tcm = runST $ evalStateT (runExceptT tcm) mempty

runTCM :: (forall s. TCM s a) -> (Either String a, [String])
runTCM tcm = second (reverse . tcLog) $ runST $ runStateT (runExceptT tcm) mempty

fresh :: TCM s Int
fresh = do
  i <- gets tcFresh
  modify $ \s -> s {tcFresh = i + 1}
  return i

level :: TCM s Level
level = gets tcLevel

enterLevel :: TCM s a -> TCM s a
enterLevel x = do
  Level l <- level
  modify $ \s -> s {tcLevel = Level $! l + 1}
  r <- x
  modify $ \s -> s {tcLevel = Level l}
  return r

log :: String -> TCM s ()
log l = modify $ \s -> s {tcLog = l : tcLog s}

addContext :: Program (Expr Annotation) Annotation Empty -> TCM s ()
addContext prog = modify $ \s -> s
  { tcContext = prog <> tcContext s
  , tcConstrs = HM.unionWith (<>) cs $ tcConstrs s
  } where
    cs = HM.fromList $ do
      (n, (DataDefinition d, _, _)) <- HM.toList prog
      ConstrDef c t <- quantifiedConstrTypes (\h -> Pi h . Annotation Irrelevant) d
      return (c, Set.fromList [(n, t)])

context :: Name -> TCM s (Definition (Expr Annotation) v, Type Annotation v, Annotation)
context v = do
  mres <- gets $ HM.lookup v . tcContext
  maybe (throwError $ "Not in scope: " ++ show v)
        (\(d, t, a) -> return (fromEmpty <$> d, fromEmpty <$> t, a))
        mres

constructor :: Ord v => Constr -> TCM s (Set (Name, Type Annotation v))
constructor c = do
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
