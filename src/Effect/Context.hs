{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
module Effect.Context(module Effect.Context, module Syntax.Context) where

import Protolude

import Control.Lens hiding (Context, (|>))
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.ListT
import Control.Monad.Trans.Maybe
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.List.Class as ListT
import Effect.Fresh

import Syntax.Annotation
import Syntax.Context
import Syntax.NameHint
import qualified Util.Tsil as Tsil
import Util.Tsil(Tsil)

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

instance HasContext e (Context e) where
  context = identity

instance HasContext e env => MonadContext e ((->) env) where
  getContext = view context
  modifyContext = local . over context

lookup :: MonadContext e m => FreeVar -> m (Binding e)
lookup v = do
  Context _ m <- getContext
  return $ HashMap.lookupDefault (panic "lookup") v m

freshExtend
  :: (MonadContext e m, MonadFresh m)
  => Binding e
  -> (FreeVar -> m a)
  -> m a
freshExtend b k = do
  v <- FreeVar <$> fresh
  extend v b $ k v

extend
  :: MonadContext e m
  => FreeVar
  -> Binding e
  -> m a
  -> m a
extend v b = modifyContext (|> (v, b))

extends
  :: (Foldable t, MonadContext e m)
  => t (FreeVar, Binding e)
  -> m a
  -> m a
extends vs k = foldr (uncurry extend) k vs

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
