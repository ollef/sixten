{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleInstances #-}
module Util where
import Bound
import Bound.Var
import Control.Applicative
import Data.Set(Set)
import qualified Data.Set as S

type Scope1 = Scope ()
type Name = String
type TCon = String
type ECon = String
type Literal = Int

data Plicitness = Implicit | Explicit
  deriving (Eq, Ord, Show)

class HasPlicitness d where
  plicitness :: d -> Plicitness

isImplicit, isExplicit :: HasPlicitness d => d -> Bool
isImplicit = (== Implicit) . plicitness
isExplicit = (== Explicit) . plicitness

instance HasPlicitness Plicitness where
  plicitness = id

data Relevance = Irrelevant | Relevant
  deriving (Eq, Ord, Show)

mostRelevant :: Relevance -> Relevance -> Relevance
mostRelevant Irrelevant b          = b
mostRelevant a          Irrelevant = a
mostRelevant Relevant   Relevant   = Relevant

leastRelevant :: Relevance -> Relevance -> Relevance
leastRelevant Relevant   b          = b
leastRelevant a          Relevant   = a
leastRelevant Irrelevant Irrelevant = Irrelevant

class HasRelevance d where
  relevance :: d -> Relevance

isIrrelevant, isRelevant :: HasRelevance d => d -> Bool
isIrrelevant = (== Irrelevant) . relevance
isRelevant   = (== Relevant)   . relevance

instance HasRelevance Relevance where
  relevance = id

instance HasRelevance Plicitness where
  relevance _ = Relevant

-- | Something that is just a decoration, and not e.g. considered in comparisons.
newtype Hint a = Hint a
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

toSet ::  (Ord a, Foldable f) => f a -> Set a
toSet = foldMap S.singleton

data Empty
fromEmpty :: Empty -> a
fromEmpty = error "fromEmpty"
