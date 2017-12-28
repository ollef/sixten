module Inference.TypeCheck.Clause where

import Control.Monad.Except
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable as Foldable
import Data.List.NonEmpty(NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Monoid
import qualified Data.Vector as Vector
import Data.Void

import Inference.Class as Class
import Inference.Match as Match
import Inference.Meta
import Inference.Monad
import Inference.Subtype
import Inference.TypeCheck.Pattern
import {-# SOURCE #-} Inference.TypeCheck.Expr
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete.Scoped as Concrete
import Util
import VIX

checkClauses
  :: NonEmpty (Concrete.Clause Void Concrete.Expr MetaA)
  -> Polytype
  -> Infer AbstractM
checkClauses clauses polyType = do
  forM_ clauses $ logMeta 20 "checkClauses clause"
  logMeta 20 "checkClauses typ" polyType

  modifyIndent succ

  (rhoType, f) <- skolemise polyType $ minimum $ instUntilClause <$> clauses

  ps <- piPlicitnesses rhoType

  clauses' <- forM clauses $ \(Concrete.Clause pats body) -> do
    pats' <- equalisePats ps $ Vector.toList pats
    return $ Concrete.Clause (Vector.fromList pats') body

  let equalisedClauses = equaliseClauses clauses'

  forM_ equalisedClauses $ logMeta 20 "checkClauses equalisedClause"

  res <- checkClausesRho equalisedClauses rhoType

  modifyIndent pred
  l <- level
  logMeta 20 ("checkClauses res " <> show l) res

  f res
  where
    instUntilClause :: Concrete.Clause Void Concrete.Expr v -> InstUntil
    instUntilClause (Concrete.Clause pats s)
      | Vector.length pats > 0 = InstUntil $ fst $ Vector.head pats
      | otherwise = instUntilExpr $ fromScope s

    piPlicitnesses :: AbstractM -> Infer [Plicitness]
    piPlicitnesses t = do
      t' <- whnf t
      piPlicitnesses' t'

    piPlicitnesses' :: AbstractM -> Infer [Plicitness]
    piPlicitnesses' (Abstract.Pi h p t s) = do
      v <- forall h p t
      (:) p <$> piPlicitnesses (instantiate1 (pure v) s)
    piPlicitnesses' _ = return mempty

checkClausesRho
  :: NonEmpty (Concrete.Clause Void Concrete.Expr MetaA)
  -> Rhotype
  -> Infer AbstractM
checkClausesRho clauses rhoType = do
  forM_ clauses $ logMeta 20 "checkClausesRho clause"
  logMeta 20 "checkClausesRho type" rhoType

  let (ps, firstPats) = Vector.unzip ppats
        where
          Concrete.Clause ppats _ = NonEmpty.head clauses
  (argTele, returnTypeScope, fs) <- funSubtypes rhoType ps

  modifyIndent succ

  clauses' <- forM clauses $ \clause -> do
    let pats = Concrete.clausePatterns' clause
        bodyScope = Concrete.clauseScope' clause
    (pats', patVars) <- tcPats pats mempty argTele
    let body = instantiatePattern pure patVars bodyScope
        argExprs = snd3 <$> pats'
        returnType = instantiateTele id argExprs returnTypeScope
    body' <- checkRho body returnType
    return (fst3 <$> pats', body')

  modifyIndent pred

  forM_ clauses' $ \(pats, body) -> do
    forM_ pats $ logMeta 20 "checkClausesRho clause pat" <=< bitraverse showMeta pure
    logMeta 20 "checkClausesRho clause body" body

  argVars <- forTeleWithPrefixM (addTeleNames argTele $ Concrete.patternHint <$> firstPats) $ \h p s argVars ->
    forall h p $ instantiateTele pure argVars s

  let returnType = instantiateTele pure argVars returnTypeScope

  body <- matchClauses
    (Vector.toList $ pure <$> argVars)
    (NonEmpty.toList $ first Vector.toList <$> clauses')
    returnType

  logMeta 25 "checkClausesRho body res" body

  result <- foldrM
    (\(p, (f, v)) e ->
      f =<< Abstract.Lam (metaHint v) p (metaType v) <$> abstract1M v e)
    body
    (Vector.zip ps $ Vector.zip fs argVars)

  logMeta 20 "checkClausesRho res" result
  return result

--------------------------------------------------------------------------------
-- "Equalisation" -- making the clauses' number of patterns match eachother
-- by adding implicits and eta-converting
equaliseClauses
  :: NonEmpty (Concrete.Clause b Concrete.Expr v)
  -> NonEmpty (Concrete.Clause b Concrete.Expr v)
equaliseClauses clauses
  = NonEmpty.zipWith
    (uncurry etaClause)
    (go (Vector.toList . Concrete.clausePatterns <$> clauses))
    (Concrete.clauseScope <$> clauses)
  where
    go
      :: NonEmpty [(Plicitness, Concrete.Pat (Scope b expr v) ())]
      -> NonEmpty ([(Plicitness, Concrete.Pat (Scope b expr v) ())], [Plicitness])
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
      :: NonEmpty ([(Plicitness, Concrete.Pat (Scope b expr v) ())], [Plicitness])
      -> NonEmpty ([(Plicitness, Concrete.Pat (Scope b expr v) ())], [Plicitness])
    go' clausePats
      = NonEmpty.zipWith
        (\ps (pats, ps') -> (pats, ps ++ ps'))
        (snd <$> clausePats)
        (go $ fst <$> clausePats)

    numExplicit, numImplicit :: NonEmpty [(Plicitness, Concrete.Pat (Scope b expr v) ())] -> Int
    numExplicit = length . NonEmpty.filter (\xs -> case xs of
      (Explicit, _):_ -> True
      _ -> False)

    numImplicit = length . NonEmpty.filter (\xs -> case xs of
      (Implicit, _):_ -> True
      _ -> False)

    addImplicit, addExplicit
      :: [(Plicitness, Concrete.Pat (Scope b expr v) ())]
      -> ([(Plicitness, Concrete.Pat (Scope b expr v) ())], [Plicitness])
    addImplicit pats@((Implicit, _):_) = (pats, mempty)
    addImplicit pats = ((Implicit, Concrete.WildcardPat) : pats, mempty)

    addExplicit pats@((Explicit, _):_) = (pats, mempty)
    addExplicit pats = ((Explicit, Concrete.VarPat mempty ()) : pats, pure Explicit)

etaClause
  :: [(Plicitness, Concrete.Pat (Scope (Var PatternVar b) Concrete.Expr v) ())]
  -> [Plicitness]
  -> Scope (Var PatternVar b) Concrete.Expr v
  -> Concrete.Clause b Concrete.Expr v
etaClause pats extras (Scope scope)
  = Concrete.Clause
    (Vector.fromList pats)
    $ Scope
    $ Concrete.apps scope vs
  where
    numBindings = length $ concat $ Foldable.toList . snd <$> pats
    numExtras = length extras
    vs = zip extras $ pure . B . B . PatternVar <$> [numBindings - numExtras ..]
