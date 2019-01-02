{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
module Effect.Context where

import Protolude

import Control.Lens
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.ListT
import Control.Monad.Trans.Maybe
import qualified Data.List.Class as ListT

import qualified Util.Tsil as Tsil
import Util.Tsil(Tsil)

class Monad m => MonadContext v m | m -> v where
  getLocalVars :: m (Tsil v)
  default getLocalVars
    :: (MonadTrans t, MonadContext v m1, m ~ t m1)
    => m (Tsil v)
  getLocalVars = lift getLocalVars
  inUpdatedContext :: (Tsil v -> Tsil v) -> m a -> m a

newtype ContextEnv v = ContextEnv
  { _localVars :: Tsil v
  } deriving (Semigroup, Monoid)

makeLenses ''ContextEnv

class HasContextEnv v env | env -> v where
  contextEnv :: Lens' env (ContextEnv v)

instance (HasContextEnv v env, Monad m) => MonadContext v (ReaderT env m) where
  getLocalVars = view (contextEnv.localVars)
  inUpdatedContext = local . over (contextEnv.localVars)

withVar :: MonadContext v m => v -> m a -> m a
withVar v = inUpdatedContext $ \vs -> Tsil.Snoc vs v

withVars :: (MonadContext v m, Foldable t) => t v -> m a -> m a
withVars vs' = inUpdatedContext (<> Tsil.fromList (toList vs'))

------------------------------------------------------------------------------
-- mtl instances
-------------------------------------------------------------------------------
instance MonadContext v m => MonadContext v (StateT s m) where
  inUpdatedContext f (StateT s) = StateT $ inUpdatedContext f <$> s
instance MonadContext v m => MonadContext v (ListT m) where
  inUpdatedContext f (ListT mxs) = ListT $ do
    xs <- inUpdatedContext f mxs
    pure $ case xs of
      ListT.Nil -> ListT.Nil
      ListT.Cons x xs' -> ListT.Cons x $ inUpdatedContext f xs'
instance MonadContext v m => MonadContext v (ExceptT e m) where
  inUpdatedContext f (ExceptT m) = ExceptT $ inUpdatedContext f m
instance MonadContext v m => MonadContext v (MaybeT m) where
  inUpdatedContext f (MaybeT m) = MaybeT $ inUpdatedContext f m
instance MonadContext v m => MonadContext v (IdentityT m) where
  inUpdatedContext f (IdentityT m) = IdentityT $ inUpdatedContext f m
