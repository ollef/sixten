{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GADTs, OverloadedStrings #-}
module Syntax.Concrete.Definition where

import Control.Monad
import Data.Bifunctor
import Data.Bitraversable
import Data.List.NonEmpty(NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.String
import Data.Traversable
import qualified Data.Vector as Vector
import Data.Vector(Vector)

import Syntax
import Syntax.Concrete.Pattern

data PatDefinition expr v
  = PatDefinition (NonEmpty (Clause expr v))
  | PatDataDefinition (DataDef expr v)
  deriving (Foldable, Functor, Show, Traversable)

data Clause expr v = Clause
  { clausePatterns :: Vector (Plicitness, Pat (PatternScope expr v) ())
  , clauseScope :: PatternScope expr v
  } deriving (Show)

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

instance (Pretty (expr v), Monad expr, IsString v)
  => Pretty (Clause expr v) where
  prettyM (Clause pats s)
    = withNameHints (join $ nameHints . snd <$> pats) $ \ns -> do
      let go (p, pat)
            = prettyAnnotation p
            $ prettyM $ first (instantiatePatternVec (pure . fromName) ns) pat
      hsep (go <$> renamePatterns ns pats)
      <+> "=" <+> prettyM (instantiatePatternVec (pure . fromName) ns s)

instance (Pretty (expr v), Monad expr, IsString v)
  => Pretty (PatDefinition expr v) where
  prettyM (PatDefinition clauses) = vcat $ prettyM <$> clauses
  prettyM (PatDataDefinition dataDef)= prettyM dataDef

equaliseClauses :: NonEmpty (Clause expr v) -> NonEmpty (Clause expr v)
equaliseClauses clauses
  = NonEmpty.zipWith
    (Clause . Vector.fromList)
    (go (Vector.toList . clausePatterns <$> clauses))
    (clauseScope <$> clauses)
  where
    go
      :: NonEmpty [(Plicitness, Pat (PatternScope expr v) ())]
      -> NonEmpty [(Plicitness, Pat (PatternScope expr v) ())]
    go pats
      | numEx == 0 && numIm == 0 = pats
      | numEx == len = NonEmpty.zipWith (:) heads $ go tails
      | numIm == len = NonEmpty.zipWith (:) heads $ go tails
      | numIm > 0 = go $ addImplicit <$> pats
      | numEx > 0 = go $ addExplicit <$> pats
      where
        numEx = numExplicit pats
        numIm = numImplicit pats
        heads = head <$> pats
        tails = tail <$> pats
        len = length pats

    numExplicit, numImplicit :: NonEmpty [(Plicitness, Pat (PatternScope expr v) ())] -> Int
    numExplicit = length . NonEmpty.filter (\xs -> case xs of
      (Explicit, _):_ -> True
      _ -> False)

    numImplicit = length . NonEmpty.filter (\xs -> case xs of
      (Implicit, _):_ -> True
      _ -> False)

    addImplicit, addExplicit
      :: [(Plicitness, Pat (PatternScope expr v) ())]
      -> [(Plicitness, Pat (PatternScope expr v) ())]
    addImplicit pats@((Implicit, _):_) = pats
    addImplicit pats = (Implicit, WildcardPat) : pats

    addExplicit = error "addExplicit TODO"
