{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GADTs, OverloadedStrings #-}
module Syntax.Concrete.Definition where

import Control.Monad
import Data.Bifunctor
import Data.Bitraversable
import qualified Data.Foldable as Foldable
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

equaliseClauses
  :: (AppSyntax expr, Applicative expr, Annotation expr ~ Plicitness)
  => NonEmpty (Clause expr v)
  -> NonEmpty (Clause expr v)
equaliseClauses clauses
  = NonEmpty.zipWith
    (uncurry etaClause)
    (go (Vector.toList . clausePatterns <$> clauses))
    (clauseScope <$> clauses)
  where
    go
      :: NonEmpty [(Plicitness, Pat (PatternScope expr v) ())]
      -> NonEmpty ([(Plicitness, Pat (PatternScope expr v) ())], [Plicitness])
    go clausePats
      | numEx == 0 && numIm == 0 = (\pats -> (pats, mempty)) <$> clausePats
      | numEx == len = NonEmpty.zipWith (first . (:)) heads $ go tails
      | numIm == len = NonEmpty.zipWith (first . (:)) heads $ go tails
      | numIm > 0 = go' $ addImplicit <$> clausePats
      | numEx > 0 = go' $ addExplicit <$> clausePats
      | otherwise = error "equaliseClauses go"
      where
        numEx = numExplicit clausePats
        numIm = numImplicit clausePats
        heads = head <$> clausePats
        tails = tail <$> clausePats
        len = length clausePats
    go'
      :: NonEmpty ([(Plicitness, Pat (PatternScope expr v) ())], [Plicitness])
      -> NonEmpty ([(Plicitness, Pat (PatternScope expr v) ())], [Plicitness])
    go' clausePats
      = NonEmpty.zipWith
        (\ps (pats, ps') -> (pats, ps ++ ps'))
        (snd <$> clausePats)
        (go $ fst <$> clausePats)

    numExplicit, numImplicit :: NonEmpty [(Plicitness, Pat (PatternScope expr v) ())] -> Int
    numExplicit = length . NonEmpty.filter (\xs -> case xs of
      (Explicit, _):_ -> True
      _ -> False)

    numImplicit = length . NonEmpty.filter (\xs -> case xs of
      (Implicit, _):_ -> True
      _ -> False)

    addImplicit, addExplicit
      :: [(Plicitness, Pat (PatternScope expr v) ())]
      -> ([(Plicitness, Pat (PatternScope expr v) ())], [Plicitness])
    addImplicit pats@((Implicit, _):_) = (pats, mempty)
    addImplicit pats = ((Implicit, WildcardPat) : pats, mempty)

    addExplicit pats@((Explicit, _):_) = (pats, mempty)
    addExplicit pats = ((Explicit, VarPat mempty ()) : pats, pure Explicit)

etaClause
  :: (AppSyntax expr, Applicative expr, Annotation expr ~ Plicitness)
  => [(Plicitness, Pat (PatternScope expr v) ())]
  -> [Plicitness]
  -> PatternScope expr v
  -> Clause expr v
etaClause pats extras (Scope scope)
  = Clause
    (Vector.fromList pats)
    $ Scope
    $ apps scope vs
  where
    numBindings = length $ concat $ Foldable.toList . snd <$> pats
    numExtras = length extras
    vs = zip extras $ pure . B . PatternVar <$> [numBindings - numExtras ..]
