{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, GADTs #-}
module Syntax.Concrete.Definition where

import Control.Monad
import Data.Bifunctor
import Data.Bitraversable
import Data.List.NonEmpty(NonEmpty)
import Data.Monoid
import Data.Traversable
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Syntax
import Syntax.Concrete.Pattern
import Util

data PatDefinition expr v
  = PatDefinition (NonEmpty (Clause expr v))
  | PatDataDefinition (DataDef expr v)
  deriving (Foldable, Functor, Show, Traversable)

data Clause expr v
  = Clause
    (Vector (Plicitness, Pat (PatternScope expr v) ()))
    (PatternScope expr v)
  deriving (Show)

-- TODO handle plicitness
etaExpandClause
  :: (Monad expr, AppSyntax expr, Annotation expr ~ Plicitness)
  => Int
  -> Annotation expr
  -> Clause expr v
  -> Clause expr v
etaExpandClause n anno (Clause pats (Scope s))
  = Clause pats' (Scope $ apps s $ (\i -> (anno, pure $ B i)) <$> Vector.enumFromN startIndex n)
  where
    startIndex = fromIntegral $ Vector.length patVars
    patVars = join $ toVector . snd <$> pats
    pats' = pats <> Vector.replicate n (anno, VarPat mempty ())

-------------------------------------------------------------------------------
-- Instances
instance Traversable expr => Functor (Clause expr) where fmap = fmapDefault
instance Traversable expr => Foldable (Clause expr) where foldMap = foldMapDefault

instance Traversable expr => Traversable (Clause expr) where
  traverse f (Clause pats s)
    = Clause
    <$> traverse (traverse (bitraverse (traverse f) pure)) pats
    <*> traverse f s

instance GlobalBound PatDefinition where
  bound f g (PatDefinition clauses) = PatDefinition $ bound f g <$> clauses
  bound f g (PatDataDefinition dataDef) = PatDataDefinition $ bound f g dataDef

instance GlobalBound Clause where
  bound f g (Clause pats s) = Clause (fmap (first (bound f g)) <$> pats) (bound f g s)
