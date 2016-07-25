{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleInstances, GeneralizedNewtypeDeriving #-}
module Syntax.Hint where

import Control.Applicative
import Data.String

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

newtype NameHint = NameHint (Hint (Maybe Name))
  deriving (Eq, Ord, Show)

unNameHint :: NameHint -> Maybe Name
unNameHint (NameHint (Hint x)) = x

instance Monoid NameHint where
  mempty = NameHint $ Hint mempty
  mappend (NameHint (Hint a)) (NameHint (Hint b)) = NameHint $ Hint $ a <|> b

instance IsString NameHint where
  fromString = NameHint . Hint . Just . fromString
