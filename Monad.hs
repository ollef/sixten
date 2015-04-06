{-# LANGUAGE RankNTypes #-}
module Monad where
import Control.Monad.Except
import Control.Monad.State(evalStateT, StateT, runStateT, gets, modify)
import Control.Monad.ST
import Data.Bifunctor
import Data.Monoid

-- import Core

newtype Level = Level Int
  deriving (Eq, Ord, Show)

data State = State
  { -- tcTypes      :: Map Con (Type () ())
  -- , tcKinds      :: Map TCon (Kind ())
  -- , tcSynonyms   :: Map TCon (Type () ())
    tcIndent     :: {-# UNPACK #-} !Int -- This has no place here, but is useful for debugging
  , tcFresh      :: {-# UNPACK #-} !Int
  , tcLevel      :: {-# UNPACK #-} !Level
  , tcLog        :: ![String]
  }

instance Monoid State where
  mempty = State
    { -- tcTypes    = M.fromList builtinTypes
    -- , tcKinds    = M.fromList builtinKinds
    -- , tcSynonyms = mempty
      tcIndent   = 0
    , tcFresh    = 0
    , tcLevel    = Level 1
    , tcLog      = mempty
    }
    where
  mappend (State x1 y1 (Level z1) l1) (State x2 y2 (Level z2) l2)
    = State (x1 + x2) (y1 + y2) (Level $ z1 + z2) (l1 <> l2)

type TCM s a = ExceptT String (StateT State (ST s)) a

evalTCM :: (forall s. TCM s a) -> Either String a
evalTCM tcm = runST $ evalStateT (runExceptT tcm) mempty

runTCM :: (forall s. TCM s a) -> (Either String a, [String])
runTCM tcm = second tcLog $ runST $ runStateT (runExceptT tcm) mempty

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
log s = modify (<> mempty {tcLog = [s]})

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
