{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Effect.Context where

import Protolude

import Control.Lens hiding (Context)
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.ListT
import Control.Monad.Trans.Maybe
import qualified Data.List.Class as ListT

import qualified Util.Tsil as Tsil
import Util.Tsil(Tsil)
import Syntax.Context

class Monad m => MonadContext e m | m -> e where
  getContext :: m (Context e)
  default getContext
    :: (MonadTrans t, MonadContext e m1, m ~ t m1)
    => m (Context e)
  getContext = lift getContext
  modifyContext :: (Context e -> Context e) -> m a -> m a

class HasContext e env | env -> e where
  context :: Lens' env (Context e)

instance (HasContext e env, Monad m) => MonadContext e (ReaderT env m) where
  getContext = view context
  modifyContext = local . over context

------------------------------------------------------------------------------
-- mtl instances
-------------------------------------------------------------------------------
instance MonadContext e m => MonadContext e (StateT s m) where
  modifyContext f (StateT s) = StateT $ modifyContext f <$> s
instance MonadContext e m => MonadContext e (ListT m) where
  modifyContext f (ListT mxs) = ListT $ do
    xs <- modifyContext f mxs
    pure $ case xs of
      ListT.Nil -> ListT.Nil
      ListT.Cons x xs' -> ListT.Cons x $ modifyContext f xs'
instance MonadContext e m => MonadContext e (ExceptT e m) where
  modifyContext f (ExceptT m) = ExceptT $ modifyContext f m
instance MonadContext e m => MonadContext e (MaybeT m) where
  modifyContext f (MaybeT m) = MaybeT $ modifyContext f m
instance MonadContext e m => MonadContext e (IdentityT m) where
  modifyContext f (IdentityT m) = IdentityT $ modifyContext f m
