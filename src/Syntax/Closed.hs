{-# LANGUAGE UndecidableInstances, RankNTypes #-}
module Syntax.Closed where

import Data.Bifunctor
import Data.Void

newtype Closed f = Closed { open :: forall a. f a }

instance Eq (f Void) => Eq (Closed f) where
  Closed x == Closed y = voidid x == y
    where
      voidid :: f Void -> f Void
      voidid = id

instance Ord (f Void) => Ord (Closed f) where
  compare (Closed x) (Closed y) = compare (voidid x) y
    where
      voidid :: f Void -> f Void
      voidid = id

mapClosed :: (forall a. f a -> g a) -> Closed f -> Closed g
mapClosed f (Closed x) = Closed $ f x

close :: Functor f => (a -> Void) -> f a -> Closed f
close f x = Closed (absurd . f <$> x)

newtype Biclosed f = Biclosed { biopen :: forall a b. f a b }

biclose :: Bifunctor f => (a -> Void) -> (b -> Void) -> f a b -> Biclosed f
biclose f g x = Biclosed $ bimap (absurd . f) (absurd . g) x
