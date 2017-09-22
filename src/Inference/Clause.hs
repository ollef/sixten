{-# LANGUAGE TypeFamilies, OverloadedStrings #-}
module Inference.Clause where

import Control.Monad.Except
import Data.Bifunctor
import qualified Data.Foldable as Foldable
import Data.List.NonEmpty(NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Monoid
import qualified Data.Vector as Vector
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen
import Text.Trifecta.Result(Err(Err), explain)

import Syntax
import Syntax.Concrete.Scoped
import VIX

exactlyEqualisePats
  :: Pretty v
  => [Plicitness]
  -> [(Plicitness, Pat e v)]
  -> VIX [(Plicitness, Pat e v)]
exactlyEqualisePats [] [] = return []
exactlyEqualisePats [] ((p, pat):_) = do
  loc <- currentLocation
  throwError
    $ show
    $ explain loc
    $ Err (Just "Too many patterns for type")
    [ "Found the pattern:" Leijen.<+> Leijen.red (runPrettyM $ prettyAnnotation p (prettyM $ first (const ()) pat)) <> "."
    , "Expected: no more patterns."
    ]
    mempty
    mempty
exactlyEqualisePats (Implicit:ps) ((Implicit, pat):pats)
  = (:) (Implicit, pat) <$> exactlyEqualisePats ps pats
exactlyEqualisePats (Explicit:ps) ((Explicit, pat):pats)
  = (:) (Explicit, pat) <$> exactlyEqualisePats ps pats
exactlyEqualisePats (Implicit:ps) pats
  = (:) (Implicit, WildcardPat) <$> exactlyEqualisePats ps pats
exactlyEqualisePats (Explicit:_) ((Implicit, pat):_)
  = throwExpectedExplicit pat
exactlyEqualisePats (Explicit:_) [] = do
  loc <- currentLocation
  throwError
    $ show
    $ explain loc
    $ Err (Just "Not enough patterns for type")
    [ "Found the pattern: no patterns."
    , "Expected: an explicit pattern."
    ]
    mempty
    mempty

equalisePats
  :: Pretty v
  => [Plicitness]
  -> [(Plicitness, Pat e v)]
  -> VIX [(Plicitness, Pat e v)]
equalisePats _ [] = return []
equalisePats [] pats = return pats
equalisePats (Implicit:ps) ((Implicit, pat):pats)
  = (:) (Implicit, pat) <$> equalisePats ps pats
equalisePats (Explicit:ps) ((Explicit, pat):pats)
  = (:) (Explicit, pat) <$> equalisePats ps pats
equalisePats (Implicit:ps) pats
  = (:) (Implicit, WildcardPat) <$> equalisePats ps pats
equalisePats (Explicit:_) ((Implicit, pat):_)
  = throwExpectedExplicit pat

throwExpectedExplicit :: Pretty v => Pat e v -> VIX a
throwExpectedExplicit pat = do
  loc <- currentLocation
  throwError
    $ show
    $ explain loc
    $ Err (Just "Explicit/implicit mismatch")
    [ "Found the implicit pattern:" Leijen.<+> Leijen.red (runPrettyM $ prettyAnnotation Implicit (prettyM $ first (const ()) pat)) <> "."
    , "Expected:" Leijen.<+> "an" Leijen.<+> Leijen.dullgreen "explicit" Leijen.<+> "pattern."
    ]
    mempty
    mempty

equaliseClauses
  :: NonEmpty (Clause b Expr v)
  -> NonEmpty (Clause b Expr v)
equaliseClauses clauses
  = NonEmpty.zipWith
    (uncurry etaClause)
    (go (Vector.toList . clausePatterns <$> clauses))
    (clauseScope <$> clauses)
  where
    go
      :: NonEmpty [(Plicitness, Pat (Scope b expr v) ())]
      -> NonEmpty ([(Plicitness, Pat (Scope b expr v) ())], [Plicitness])
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
      :: NonEmpty ([(Plicitness, Pat (Scope b expr v) ())], [Plicitness])
      -> NonEmpty ([(Plicitness, Pat (Scope b expr v) ())], [Plicitness])
    go' clausePats
      = NonEmpty.zipWith
        (\ps (pats, ps') -> (pats, ps ++ ps'))
        (snd <$> clausePats)
        (go $ fst <$> clausePats)

    numExplicit, numImplicit :: NonEmpty [(Plicitness, Pat (Scope b expr v) ())] -> Int
    numExplicit = length . NonEmpty.filter (\xs -> case xs of
      (Explicit, _):_ -> True
      _ -> False)

    numImplicit = length . NonEmpty.filter (\xs -> case xs of
      (Implicit, _):_ -> True
      _ -> False)

    addImplicit, addExplicit
      :: [(Plicitness, Pat (Scope b expr v) ())]
      -> ([(Plicitness, Pat (Scope b expr v) ())], [Plicitness])
    addImplicit pats@((Implicit, _):_) = (pats, mempty)
    addImplicit pats = ((Implicit, WildcardPat) : pats, mempty)

    addExplicit pats@((Explicit, _):_) = (pats, mempty)
    addExplicit pats = ((Explicit, VarPat mempty ()) : pats, pure Explicit)

etaClause
  :: [(Plicitness, Pat (Scope (Var PatternVar b) Expr v) ())]
  -> [Plicitness]
  -> Scope (Var PatternVar b) Expr v
  -> Clause b Expr v
etaClause pats extras (Scope scope)
  = Clause
    (Vector.fromList pats)
    $ Scope
    $ apps scope vs
  where
    numBindings = length $ concat $ Foldable.toList . snd <$> pats
    numExtras = length extras
    vs = zip extras $ pure . B . B . PatternVar <$> [numBindings - numExtras ..]
