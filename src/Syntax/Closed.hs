{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Syntax.Closed where

import Protolude

import Pretty

newtype Closed f = Closed { open :: forall a. f a }

instance Eq (f Void) => Eq (Closed f) where
  Closed x == Closed y = (x :: f Void) == y

instance Ord (f Void) => Ord (Closed f) where
  compare (Closed x) (Closed y) = compare (x :: f Void) y

instance Hashable (f Void) => Hashable (Closed f) where
  hashWithSalt salt (Closed x) = hashWithSalt salt (x :: f Void)

instance Pretty (f Doc) => Pretty (Closed f) where
  prettyM f = prettyM (open f :: f Doc)

mapClosed :: (forall a. f a -> g a) -> Closed f -> Closed g
mapClosed f (Closed x) = Closed $ f x

close :: Functor f => (a -> Void) -> f a -> Closed f
close f x = Closed (absurd . f <$> x)

newtype Biclosed f = Biclosed { biopen :: forall a b. f a b }

biclose :: Bifunctor f => (a -> Void) -> (b -> Void) -> f a b -> Biclosed f
biclose f g x = Biclosed $ bimap (absurd . f) (absurd . g) x

instance Hashable (f Void Void) => Hashable (Biclosed f) where
  hashWithSalt salt (Biclosed x) = hashWithSalt salt (x :: f Void Void)
