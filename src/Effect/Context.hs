{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
module Effect.Context(module Effect.Context, module Syntax.Context) where

import Protolude

import Control.Lens hiding (Context, (|>))
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.ListT
import Control.Monad.Trans.Maybe
import Data.Char
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.List.Class as ListT

import qualified Data.Text as Text
import Effect.Fresh
import Pretty
import Syntax.Annotation
import Syntax.Context
import Syntax.Name
import Syntax.NameHint
import Util
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

lookupHint :: MonadContext e m => FreeVar -> m NameHint
lookupHint = fmap _hint . lookup

lookupType :: MonadContext e m => FreeVar -> m e
lookupType = fmap _type . lookup

lookupPlicitness :: MonadContext e m => FreeVar -> m Plicitness
lookupPlicitness = fmap _plicitness . lookup

lookupValue :: MonadContext e m => FreeVar -> m (Maybe e)
lookupValue = fmap _value . lookup

freshExtend
  :: (MonadContext e m, MonadFresh m)
  => Binding e
  -> (FreeVar -> m a)
  -> m a
freshExtend b k = do
  v <- FreeVar <$> fresh
  extend v b $ k v

freshExtends
  :: (MonadContext e m, MonadFresh m, Traversable t)
  => t (Binding e)
  -> (t FreeVar -> m a)
  -> m a
freshExtends bs k = do
  v <- FreeVar <$> fresh
  vs <- traverse (\b -> (,b) . FreeVar <$> fresh) bs
  extends vs $ k $ fst <$> vs

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

prettyVar
  :: MonadContext e m
  => FreeVar
  -> m Doc
prettyVar v@(FreeVar i) = do
  Binding h p t _ <- lookup v
  return $ case () of
    ()
      | Text.null hintText -> "$" <> shower i
      | isDigit (Text.last hintText) -> "$" <> hint <> "-" <> shower i
      | otherwise -> "$" <> hint <> shower i
      where
        hintText = fromNameHint mempty fromName h
        hint = pretty hintText

set
  :: MonadContext e m
  => FreeVar
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
  => f (FreeVar, e)
  -> m a
  -> m a
sets xs = modifyContext go
  where
    f m (v, e) = HashMap.adjust (\(Binding h p t _) -> Binding h p t $ Just e) v m
    go (Context vs m) = Context vs $ foldl' f m xs

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
