{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
module Syntax.Binds where

import Bound.Var
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Functor.Classes

class (Monad m, Functor f) => Binds m f | f -> m where
  (>>>=) :: f a -> (a -> m b) -> f b

bindsJoin :: Binds m f => f (m a) -> f a
bindsJoin x = x >>>= id

-------------------------------------------------------------------------------
-- * Scopes
-- | Scopes of `f` structures with free variables in `a`, binding `m`
-- expressions
newtype Scope m b f a = Scope { unscope :: f (Var b (m a)) }
  deriving (Functor, Foldable, Traversable)

type Scope1 m = Scope m ()

instantiate :: Binds m f => (b -> m a) -> Scope m b f a -> f a
instantiate f (Scope s) = s >>>= unvar f id

instantiate1 :: Binds m f => m a -> Scope1 m f a -> f a
instantiate1 x s = instantiate (\_ -> x) s

abstract :: (Applicative m, Functor f) => (a -> Maybe b) -> f a -> Scope m b f a
abstract f m = Scope $ go <$> m
  where
    go x = case f x of
      Nothing -> F $ pure x
      Just b -> B b

fromScope :: Binds m f => Scope m b f a -> f (Var b a)
fromScope (Scope s) = s >>>= unvar (pure . B) (fmap F)

toScope :: Binds m f => f (Var b a) -> Scope m b f a
toScope f = Scope $ fmap pure <$> f

transverseScope
  :: (Applicative f, Monad f, Traversable g)
  => (forall r. g r -> f (h r))
  -> Scope m b g a -> f (Scope m b h a)
transverseScope f (Scope s) = Scope <$> _ s

bimapScope
  :: (Bifunctor t, Functor m)
  => (k -> k')
  -> (a -> a')
  -> Scope m b (t k) a
  -> Scope m b (t k') a'
bimapScope f g (Scope s) = Scope $ bimap f (fmap $ fmap g) s

bimapScope'
  :: Bifunctor f
  => (x -> x')
  -> (y -> y')
  -> Scope (f x) b (f x) y
  -> Scope (f x') b (f x') y'
bimapScope' f g (Scope s) = Scope $ bimap f (fmap $ bimap f g) s

bifoldMapScope
  :: (Foldable m, Bifoldable f, Monoid r)
  => (x -> r)
  -> (y -> r)
  -> Scope m b (f x) y
  -> r
bifoldMapScope f g (Scope s) = bifoldMap f (foldMap $ foldMap g) s

bifoldMapScope'
  :: (Bifoldable f, Monoid r)
  => (x -> r)
  -> (y -> r)
  -> Scope (f x) b (f x) y
  -> r
bifoldMapScope' f g (Scope s) = bifoldMap f (foldMap $ bifoldMap f g) s

bitraverseScope
  :: (Bitraversable t, Traversable m, Applicative f)
  => (k -> f k')
  -> (a -> f a')
  -> Scope m b (t k) a
  -> f (Scope m b (t k') a')
bitraverseScope f g (Scope s) = Scope <$> bitraverse f (traverse $ traverse g) s

bitraverseScope'
  :: (Bitraversable t, Applicative f)
  => (k -> f k')
  -> (a -> f a')
  -> Scope (t k) b (t k) a
  -> f (Scope (t k') b (t k') a')
bitraverseScope' f g (Scope s) = Scope <$> bitraverse f (traverse $ bitraverse f g) s

mapBound :: Functor f => (b -> b') -> Scope m b f a -> Scope m b' f a
mapBound f (Scope s) = Scope $ fmap (first f) s

-------------------------------------------------------------------------------
-- Instances
instance (Read1 m, Read b, Read1 f, Read a) => Read (Scope m b f a) where readsPrec = readsPrec1
instance (Show1 m, Show b, Show1 f, Show a) => Show (Scope m b f a) where showsPrec = showsPrec1

instance (Binds m f, Eq b, Eq1 f) => Eq1 (Scope m b f) where
  liftEq f m n = liftEq (liftEq f) (fromScope m) (fromScope n)

instance (Binds m f, Eq b, Eq1 f, Eq a) => Eq (Scope m b f a) where
  (==) = liftEq (==)

instance (Binds m f, Ord b, Ord1 f) => Ord1 (Scope m b f) where
  liftCompare f m n = liftCompare (liftCompare f) (fromScope m) (fromScope n)

instance (Binds m f, Ord b, Ord1 f, Ord a) => Ord (Scope m b f a) where
  compare = liftCompare compare

instance (Show1 m, Show b, Show1 f) => Show1 (Scope m b f) where
  liftShowsPrec f g d m = showsUnaryWith (liftShowsPrec (liftShowsPrec f' g') (liftShowList f' g')) "Scope" d (unscope m) where
    f' = liftShowsPrec f g
    g' = liftShowList f g

instance (Read1 m, Read b, Read1 f) => Read1 (Scope m b f) where
  liftReadsPrec f g = readsData $ readsUnaryWith (liftReadsPrec (liftReadsPrec f' g') (liftReadList f' g')) "Scope" Scope where
    f' = liftReadsPrec f g
    g' = liftReadList f g

instance Binds m f => Binds m (Scope m b f) where
  Scope s >>>= f = Scope $ s >>>= unvar (pure . B) (fmap $ F . f)
