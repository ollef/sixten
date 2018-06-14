{-# LANGUAGE DefaultSignatures, FlexibleInstances, FunctionalDependencies, GADTs, MultiParamTypeClasses, UndecidableInstances #-}
module MonadContext where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Identity
import Control.Monad.Writer

import Util.Tsil

class Monad m => MonadContext v m | m -> v where
  inUpdatedContext :: (Tsil v -> Tsil v) -> m a -> m a
  localVars :: m (Tsil v)

  default localVars
    :: (MonadTrans t, MonadContext v m1, m ~ t m1)
    => m (Tsil v)
  localVars = lift localVars

withVar :: MonadContext v m => v -> m a -> m a
withVar v = inUpdatedContext $ \vs -> Snoc vs v

withVars :: (MonadContext v m, Foldable t) => t v -> m a -> m a
withVars vs m = foldr withVar m vs

-------------------------------------------------------------------------------
-- mtl instances
-------------------------------------------------------------------------------
instance MonadContext v m => MonadContext v (ReaderT r m) where
  inUpdatedContext f (ReaderT m) = ReaderT $ inUpdatedContext f . m
instance (Monoid w, MonadContext v m) => MonadContext v (WriterT w m) where
  inUpdatedContext f (WriterT m) = WriterT $ inUpdatedContext f m
instance MonadContext v m => MonadContext v (StateT s m) where
  inUpdatedContext f (StateT m) = StateT $ inUpdatedContext f . m
instance MonadContext v m => MonadContext v (IdentityT m) where
  inUpdatedContext f (IdentityT m) = IdentityT $ inUpdatedContext f m
