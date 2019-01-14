{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FunctionalDependencies #-}
module Effect.Fresh where

import Protolude

import Control.Lens
import Control.Monad.Except
import Control.Monad.ListT
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Writer
import qualified LLVM.IRBuilder as IRBuilder

class Monad m => MonadFresh m where
  fresh :: m Int

  default fresh
    :: (MonadTrans t, MonadFresh m1, m ~ t m1)
    => m Int
  fresh = lift fresh

newtype FreshEnv = FreshEnv
  { _freshVar :: MVar Int
  }

emptyFreshEnv :: MonadIO m => m FreshEnv
emptyFreshEnv = FreshEnv <$> liftIO (newMVar 0)

makeLenses ''FreshEnv

class HasFreshEnv env where
  freshEnv :: Lens' env FreshEnv

instance (HasFreshEnv env, MonadIO m) => MonadFresh (ReaderT env m) where
  fresh = do
    v <- view $ freshEnv.freshVar
    liftIO $ modifyMVar v $ \i -> pure (i + 1, i)

-------------------------------------------------------------------------------
-- mtl instances
-------------------------------------------------------------------------------
instance (Monoid w, MonadFresh m) => MonadFresh (WriterT w m)
instance MonadFresh m => MonadFresh (StateT s m)
instance MonadFresh m => MonadFresh (IdentityT m)
instance MonadFresh m => MonadFresh (IRBuilder.IRBuilderT m)
instance MonadFresh m => MonadFresh (IRBuilder.ModuleBuilderT m)
instance MonadFresh m => MonadFresh (ExceptT e m)
instance MonadFresh m => MonadFresh (MaybeT m)
instance MonadFresh m => MonadFresh (ListT m)
