{-# LANGUAGE RankNTypes #-}
module Monad where
import Control.Monad.Except
import Control.Monad.State(evalStateT, StateT, runStateT, gets, modify)
import Control.Monad.ST
import Data.Bifunctor
import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import Data.Monoid

import Annotation
import Core
import Pretty

newtype Level = Level Int
  deriving (Eq, Ord, Show)

instance Pretty Level where
  pretty (Level i) = pretty i

data State v = State
  { tcContext    :: Program Annotation v
  , tcIndent     :: {-# UNPACK #-} !Int -- This has no place here, but is useful for debugging
  , tcFresh      :: {-# UNPACK #-} !Int
  , tcLevel      :: {-# UNPACK #-} !Level
  , tcLog        :: ![String]
  }

instance (Eq v, Hashable v) => Monoid (State v) where
  mempty = State
    { tcContext  = mempty
    , tcIndent   = 0
    , tcFresh    = 0
    , tcLevel    = Level 1
    , tcLog      = mempty
    }
    where
  mappend (State cxt1 x1 y1 (Level z1) l1) (State cxt2 x2 y2 (Level z2) l2)
    = State (cxt1 <> cxt2) (x1 + x2) (y1 + y2) (Level $ z1 + z2) (l1 <> l2)

type TCM s v a = ExceptT String (StateT (State v) (ST s)) a

evalTCM :: (Eq v, Hashable v) => (forall s. TCM s v a) -> Either String a
evalTCM tcm = runST $ evalStateT (runExceptT tcm) mempty

runTCM :: (Eq v, Hashable v) => (forall s. TCM s v a) -> (Either String a, [String])
runTCM tcm = second (reverse . tcLog) $ runST $ runStateT (runExceptT tcm) mempty

fresh :: TCM s v Int
fresh = do
  i <- gets tcFresh
  modify $ \s -> s {tcFresh = i + 1}
  return i

level :: TCM s v Level
level = gets tcLevel

enterLevel :: TCM s v a -> TCM s v a
enterLevel x = do
  Level l <- level
  modify $ \s -> s {tcLevel = Level $! l + 1}
  r <- x
  modify $ \s -> s {tcLevel = Level l}
  return r

log :: String -> TCM s v ()
log l = modify $ \s -> s {tcLog = l : tcLog s}

addContext :: (Eq v, Hashable v) => Program Annotation v -> TCM s v ()
addContext p = modify $ \s -> s {tcContext = p <> tcContext s}

context :: (Eq v, Hashable v, Show v)
        => v -> TCM s v (Expr Annotation v, Type Annotation v, Annotation)
context v = do
  mres <- gets $ HM.lookup v . tcContext
  maybe (throwError $ "Not in scope: " ++ show v) return mres

modifyIndent :: (Int -> Int) -> TCM s v ()
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
