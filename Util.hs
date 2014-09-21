{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Util where
import Data.Foldable
import Data.Traversable

import Bound
import Pretty

type Scope1 = Scope ()
type Name = String

data Plicitness = Implicit | Explicit
  deriving (Eq, Ord, Show)

-- | Something that is just a decoration, and not e.g. considered in equality comparisons.
newtype Hint a = Hint {unHint :: a}
  deriving (Foldable, Functor, Show, Traversable)

instance Pretty a => Pretty (Hint a) where pretty = pretty . unHint

instance Eq (Hint a) where
  _ == _ = True

instance Ord (Hint a) where
  compare _ _ = EQ
