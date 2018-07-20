{-# LANGUAGE DeriveFunctor, DeriveTraversable #-}
module Util.Tsil where

import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Semigroup

data Tsil a
  = Nil | Snoc (Tsil a) a
  deriving (Eq, Functor, Ord, Show, Traversable)

instance Semigroup (Tsil a) where
  xs <> Nil = xs
  xs <> Snoc ys y = Snoc (xs <> ys) y

instance Monoid (Tsil a) where
  mempty = Nil
  mappend = (<>)

instance Applicative Tsil where
  pure = Snoc Nil
  (<*>) = ap

instance Alternative Tsil where
  empty = Nil
  (<|>) = mappend

instance Monad Tsil where
  return = pure
  Nil >>= _ = Nil
  Snoc xs x >>= f = (xs >>= f) <> f x

fromList :: [a] -> Tsil a
fromList = foldr (flip Snoc) Nil . reverse

instance Foldable Tsil where
  foldMap _ Nil = mempty
  foldMap f (Snoc xs x) = foldMap f xs `mappend` f x

  toList = reverse . go
    where
      go Nil = []
      go (Snoc xs x) = x : go xs

lookup :: Eq a => a -> Tsil (a, b) -> Maybe b
lookup _ Nil = Nothing
lookup a (Snoc as (a', b))
  | a == a' = Just b
  | otherwise = Util.Tsil.lookup a as

filter :: (a -> Bool) -> Tsil a -> Tsil a
filter _ Nil = Nil
filter f (Snoc xs x)
  | f x = Snoc (Util.Tsil.filter f xs) x
  | otherwise = Util.Tsil.filter f xs
