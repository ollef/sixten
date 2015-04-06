{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Util where
import Bound
import Bound.Var

type Scope1 = Scope ()
type Name = String
type TCon = String
type ECon = String
type Literal = Int

data Plicitness = Implicit | Explicit
  deriving (Eq, Ord, Show)

-- | Something that is just a decoration, and not e.g. considered in comparisons.
newtype Hint a = Hint {unHint :: a}
  deriving (Foldable, Functor, Show, Traversable)

instance Eq (Hint a) where
  _ == _ = True

instance Ord (Hint a) where
  compare _ _ = EQ

type NameHint = Hint (Maybe Name)

unused :: (Monad f, Traversable f) => f (Var b a) -> Maybe (f a)
unused = traverse $ unvar (const Nothing) pure

unusedScope :: (Monad f, Traversable f) => Scope b f a -> Maybe (f a)
unusedScope = unused . fromScope
