{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleInstances #-}
module Syntax.Hint where

import Control.Applicative

import Syntax.Name

-- | Something that is just a decoration, and not e.g. considered in
--   comparisons.
newtype Hint a = Hint a
  deriving (Foldable, Functor, Show, Traversable)

unHint :: Hint a -> a
unHint (Hint x) = x

instance Eq (Hint a) where
  _ == _ = True

instance Ord (Hint a) where
  compare _ _ = EQ

type NameHint = Hint (Maybe Name)

-- | Alternative means that 'Just's don't get appended if 'm' is 'Maybe'
instance Alternative m => Monoid (Hint (m a)) where
  mempty = Hint empty
  mappend (Hint a) (Hint b) = Hint (a <|> b)
