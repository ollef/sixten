{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
module Effect.Context(module Effect.Context, module Syntax.Context) where

import Protolude
import qualified Prelude

import Control.Lens hiding (Context, (:>))
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.ListT
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Data.Char
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.List.Class as ListT

import qualified Data.Text as Text
import Effect.Fresh
import Effect.Log
import Effect.Report
import Pretty
import Syntax.Annotation
import Syntax.Context
import Syntax.Name
import Syntax.NameHint
import Util

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

lookup :: (HasCallStack, MonadContext e m) => Var -> m (Binding e)
lookup v = do
  Context _ m <- getContext
  return $ HashMap.lookupDefault (Prelude.error $ "lookup " <> show v) v m

lookupHint :: (MonadContext e m, HasCallStack) => Var -> m NameHint
lookupHint = fmap _hint . lookup

lookupType :: MonadContext e m => Var -> m e
lookupType = fmap _type . lookup

lookupPlicitness :: MonadContext e m => Var -> m Plicitness
lookupPlicitness = fmap _plicitness . lookup

lookupValue :: MonadContext e m => Var -> m (Maybe e)
lookupValue = fmap _value . lookup

freshExtend
  :: (MonadContext e m, MonadFresh m)
  => Binding e
  -> (Var -> m a)
  -> m a
freshExtend b k = do
  v <- freeVar
  extend v b $ k v

freshExtends
  :: (MonadContext e m, MonadFresh m, Traversable t)
  => t (Binding e)
  -> (t Var -> m a)
  -> m a
freshExtends bs k = do
  vs <- traverse (\b -> (,b) <$> freeVar) bs
  extends vs $ k $ fst <$> vs

extend
  :: MonadContext e m
  => Var
  -> Binding e
  -> m a
  -> m a
extend v b = modifyContext (:> (v, b))

extends
  :: (Foldable t, MonadContext e m)
  => t (Var, Binding e)
  -> m a
  -> m a
extends vs = modifyContext $ \ctx -> foldl (:>) ctx vs

prettyVar
  :: (MonadContext e m, HasCallStack)
  => Var
  -> m Doc
prettyVar v@(Var i) = do
  h <- lookupHint v
  return $ case () of
    ()
      | Text.null hintText -> "$" <> shower i
      | isDigit (Text.last hintText) -> "$" <> hint <> "-" <> shower i
      | otherwise -> "$" <> hint <> shower i
      where
        hintText = fromNameHint mempty fromName h
        hint = pretty hintText

prettyContext :: MonadContext e m => (e -> m Doc) -> m Doc
prettyContext f = do
  Context vs _ <- getContext
  fmap pretty $ forM (toList vs) $ \v -> do
    Binding _ _ t mval <- lookup v
    pt <- f t
    pv <- prettyVar v
    case mval of
      Nothing -> return $ pv <> " : " <> pt
      Just val -> do
        pval <- f val
        return $ pv <> " : " <> pt <> " = " <> pval

update
  :: MonadContext e m
  => Var
  -> (Binding e -> Binding e)
  -> m a
  -> m a
update v f = modifyContext $ \(Context vs m) -> Context vs $ HashMap.update (Just . f) v m

updates
  :: (Foldable t, MonadContext e m)
  => t (Var, Binding e -> Binding e)
  -> m a
  -> m a
updates vs k = foldr (uncurry update) k vs

set
  :: MonadContext e m
  => Var
  -> e
  -> m a
  -> m a
set v e = modifyContext go
  where
    go (Context vs m)
      = Context
        vs
        (HashMap.adjust (\(Binding h p t _) -> Binding h p t $ Just e) v m)

sets
  :: (MonadContext e m, Foldable f)
  => f (Var, e)
  -> m a
  -> m a
sets xs = modifyContext go
  where
    f m (v, e) = HashMap.adjust (\(Binding h p t _) -> Binding h p t $ Just e) v m
    go (Context vs m) = Context vs $ foldl' f m xs

------------------------------------------------------------------------------

data ContextEnvT e env = ContextEnvT
  { _contextEnvContext :: !(Context e)
  , _contextEnvEnv :: !env
  }

makeLenses ''ContextEnvT

instance HasLogEnv env => HasLogEnv (ContextEnvT e env) where
  logEnv = contextEnvEnv.logEnv

instance HasReportEnv env => HasReportEnv (ContextEnvT e env) where
  reportEnv = contextEnvEnv.reportEnv

instance HasFreshEnv env => HasFreshEnv (ContextEnvT e env) where
  freshEnv = contextEnvEnv.freshEnv

instance HasContext e (ContextEnvT e env) where
  context = contextEnvContext

withContextEnvT
  :: ReaderT (ContextEnvT e env) m a
  -> ReaderT env m a
withContextEnvT = withReaderT $ \env -> ContextEnvT
  { _contextEnvContext = mempty
  , _contextEnvEnv = env
  }

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
instance MonadContext e m => MonadContext e (ExceptT err m) where
  modifyContext f (ExceptT m) = ExceptT $ modifyContext f m
instance MonadContext e m => MonadContext e (MaybeT m) where
  modifyContext f (MaybeT m) = MaybeT $ modifyContext f m
instance MonadContext e m => MonadContext e (IdentityT m) where
  modifyContext f (IdentityT m) = IdentityT $ modifyContext f m
