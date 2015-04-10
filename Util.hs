{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleInstances #-}
module Util where
import Control.Applicative
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

-- | Alternative means that 'Just's don't get appended
instance Alternative m => Monoid (Hint (m a)) where
  mempty = Hint empty
  mappend (Hint a) (Hint b) = Hint (a <|> b)

unusedVar :: (Monad f, Traversable f) => f (Var b a) -> Maybe (f a)
unusedVar = traverse $ unvar (const Nothing) pure

unusedScope :: (Monad f, Traversable f) => Scope b f a -> Maybe (f a)
unusedScope = unusedVar . fromScope

abstractNothing :: Monad f => f a -> Scope b f a
abstractNothing = Scope . return . F

