{-# LANGUAGE DeriveFunctor, DeriveTraversable #-}
module Util.Tsil where

import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Monoid

data Tsil a
  = Nil | Snoc (Tsil a) a
  deriving (Eq, Functor, Ord, Show, Traversable)

instance Monoid (Tsil a) where
  mempty = Nil
  xs `mappend` Nil = xs
  xs `mappend` Snoc ys y = Snoc (xs `mappend` ys) y

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
  foldMap f (Snoc xs x) = foldMap f xs <> f x

  toList = reverse . go
    where
      go Nil = []
      go (Snoc xs x) = x : go xs

lookup :: Eq a => a -> Tsil (a, b) -> Maybe b
lookup _ Nil = Nothing
lookup a (Snoc as (a', b))
  | a == a' = Just b
  | otherwise = Util.Tsil.lookup a as
