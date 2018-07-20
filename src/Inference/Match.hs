{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Inference.Match where

import Control.Monad.Except
import Data.Bifunctor
import Data.Foldable
import Data.Function
import Data.List.NonEmpty(NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Vector as Vector
import Data.Vector(Vector)

import qualified Analysis.Simplify as Simplify
import qualified Builtin.Names as Builtin
import Inference.Constraint
import Inference.MetaVar
import Inference.Monad
import Inference.TypeOf
import MonadContext
import Syntax
import Syntax.Core
import Syntax.Core.Pattern
import TypedFreeVar
import Util
import VIX

type PatM = Pat CoreM FreeV
-- | An expression possibly containing a pattern-match failure variable
type ExprF = CoreM
type Clause =
  ( [PatM]
  , ExprF
  )

fatBar :: FreeV -> CoreM -> CoreM -> CoreM
fatBar failVar e e' = case filter (== failVar) $ toList e of
  _ | Simplify.duplicable e' -> dup
  [] -> e
  [_] -> dup
  _ -> Simplify.let_
    (const False)
    mempty
    (Lam mempty Explicit Builtin.UnitType $ abstractNone e')
    (Pi mempty Explicit Builtin.UnitType $ abstractNone $ varType failVar)
    $ abstract1 failVar
    $ substitute failVar (App (pure failVar) Explicit Builtin.MkUnit) e
  where
    dup = substitute failVar e' e

matchSingle
  :: CoreM
  -> PatM
  -> CoreM
  -> CoreM
  -> Infer ExprF
matchSingle expr pat innerExpr retType = do
  failVar <- forall "fail" Explicit retType
  result <- withVar failVar $ match failVar retType [expr] [([pat], innerExpr)] innerExpr
  return $ substitute failVar (Builtin.Fail retType) result

matchCase
  :: CoreM
  -> [(PatM, CoreM)]
  -> CoreM
  -> Infer ExprF
matchCase expr pats retType = do
  failVar <- forall "fail" Explicit retType
  result <- withVar failVar $ match failVar retType [expr] (first pure <$> pats) (pure failVar)
  return $ substitute failVar (Builtin.Fail retType) result

matchClauses
  :: [CoreM]
  -> [([PatM], CoreM)]
  -> CoreM
  -> Infer ExprF
matchClauses exprs pats retType = do
  failVar <- forall "fail" Explicit retType
  result <- withVar failVar $ match failVar retType exprs pats (pure failVar)
  return $ substitute failVar (Builtin.Fail retType) result

type Match
  = FreeV -- ^ Failure variable
  -> ExprF -- ^ Return type
  -> [CoreM] -- ^ Expressions to case on corresponding to the patterns in the clauses (usually variables)
  -> [Clause] -- ^ Clauses
  -> ExprF -- ^ The continuation for pattern match failure
  -> Infer ExprF

type NonEmptyMatch
  = FreeV -- ^ Failure variable
  -> ExprF -- ^ Return type
  -> [CoreM] -- ^ Expressions to case on corresponding to the patterns in the clauses (usually variables)
  -> NonEmpty Clause -- ^ Clauses
  -> ExprF -- ^ The continuation for pattern match failure
  -> Infer ExprF

-- | Desugar pattern matching clauses
match :: Match
match _ _ _ [] expr0 = return expr0
match failVar _ [] clauses expr0 = return $ foldr go expr0 clauses
  where
    go :: Clause -> ExprF -> ExprF
    go ([], s) x = fatBar failVar s x
    go _ _ = error "match go"
match failVar retType xs clauses expr0
  = foldrM
    (matchMix failVar retType xs)
    expr0
  $ NonEmpty.groupBy ((==) `on` patternType . firstPattern) clauses

firstPattern :: ([c], b) -> c
firstPattern ([], _) = error "Match.firstPattern"
firstPattern (c:_, _) = c

matchMix :: NonEmptyMatch
matchMix failVar retType (expr:exprs) clauses@(clause NonEmpty.:| _) expr0
  = f expr failVar retType exprs clauses expr0
  where
    f = case patternType $ firstPattern clause of
      VarPatType -> matchVar
      LitPatType -> matchLit
      ConPatType -> matchCon
      ViewPatType _ -> matchView
matchMix _ _ _ _ _ = error "matchMix"

matchCon :: CoreM -> NonEmptyMatch
matchCon expr failVar retType exprs clauses expr0 = do
  let (QConstr typeName _) = firstCon $ NonEmpty.head clauses
  cs <- constructors typeName

  cbrs <- forM cs $ \c -> do
    let clausesStartingWithC = NonEmpty.filter ((== c) . firstCon) clauses
    params <- case clausesStartingWithC of
      firstClause:_ -> return $ typeParams $ firstPattern firstClause
      [] -> do
        typ <- typeOf expr
        typ' <- whnf typ
        let (_, params) = appsView typ'
        return $ Vector.fromList params
    ys <- conPatArgs c params

    let exprs' = (pure <$> Vector.toList ys) ++ exprs
    rest <- withVars ys $ match failVar retType exprs' (decon clausesStartingWithC) (pure failVar)
    return $ conBranchTyped c ys rest

  return $ fatBar failVar (Case expr (ConBranches cbrs) retType) expr0
  where
    firstCon (c:_, _) = constr c
    firstCon _ = error "firstCon "
    typeParams (ConPat _ ps _) = ps
    typeParams _ = error "match typeParams"
    constr (ConPat c _ _) = c
    constr _ = error "match constr"
    constructors typeName = do
      (DataDefinition (DataDef _ cs) _, _) <- definition typeName
      return $ QConstr typeName . constrName <$> cs

conPatArgs
  :: QConstr
  -> Vector (Plicitness, CoreM)
  -> Infer (Vector FreeV)
conPatArgs c params = do
  ctype <- qconstructor c
  let (tele, _) = pisView ctype
      tele' = instantiatePrefix (snd <$> params) tele
  forTeleWithPrefixM tele' $ \h p s vs ->
    forall h p $ instantiateTele pure vs s

matchLit :: CoreM -> NonEmptyMatch
matchLit expr failVar retType exprs clauses expr0 = do
  let ls = NonEmpty.nub $ (lit . firstPattern) <$> clauses
  lbrs <- forM ls $ \l -> do
    let clausesStartingWithL = NonEmpty.filter ((== LitPat l) . firstPattern) clauses
    rest <- match failVar retType exprs (decon clausesStartingWithL) (pure failVar)
    return $ LitBranch l rest
  return $ Case expr (LitBranches lbrs expr0) retType
  where
    lit (LitPat l) = l
    lit _ = error "match lit"

matchVar :: CoreM -> NonEmptyMatch
matchVar expr failVar retType exprs clauses expr0 = do
  let clauses' = go <$> clauses
  match failVar retType exprs (NonEmpty.toList clauses') expr0
  where
    go :: Clause -> Clause
    go (VarPat _ y:ps, e) = do
      let ps' = fmap (first $ substitute y expr) ps
      (ps', substitute y expr e)
    go _ = error "match var"

matchView :: CoreM -> NonEmptyMatch
matchView expr failVar retType exprs clauses
  = match failVar retType (App f Explicit expr : exprs) $ NonEmpty.toList $ deview <$> clauses
  where
    f = case clauses of
      (ViewPat t _:_, _) NonEmpty.:| _ -> t
      _ -> error "error matchView f"
    deview :: Clause -> Clause
    deview (ViewPat _ p:ps, s) = (p : ps, s)
    deview _ = error "error matchView deview"

decon :: [Clause] -> [Clause]
decon clauses = [(unpat pat <> pats, b) | (pat:pats, b) <- clauses]
  where
    unpat (ConPat _ _ pats) = Vector.toList $ snd3 <$> pats
    unpat (LitPat _) = mempty
    unpat _ = error "match unpat"
