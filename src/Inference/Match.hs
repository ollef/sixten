{-# LANGUAGE OverloadedStrings #-}
module Inference.Match where

import Control.Monad.Except
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import Data.Function
import Data.List.NonEmpty(NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Monoid
import qualified Data.Vector as Vector
import Data.Vector(Vector)

import qualified Analysis.Simplify as Simplify
import qualified Builtin.Names as Builtin
import Inference.Normalise
import Inference.TypeOf
import Meta
import Syntax
import Syntax.Abstract
import Syntax.Abstract.Pattern
import Util
import VIX

type PatM = Pat AbstractM MetaA
-- | An expression possibly containing a pattern-match failure variable
type ExprF = AbstractM
type Clause =
  ( [PatM]
  , ExprF
  )

fatBar :: MetaA -> AbstractM -> AbstractM -> AbstractM
fatBar failVar e e' = case filter (== failVar) $ toList e of
  _ | Simplify.duplicable e' -> dup
  [] -> e
  [_] -> dup
  _ -> Let mempty (Lam mempty Explicit Builtin.UnitType $ abstractNone e')
    $ abstract1 failVar
    $ subst1 failVar (App (pure failVar) Explicit Builtin.MkUnit) e
  where
    dup = subst1 failVar e' e

matchSingle
  :: AbstractM
  -> PatM
  -> AbstractM
  -> AbstractM
  -> VIX ExprF
matchSingle expr pat innerExpr retType = do
  failVar <- forall "fail" retType
  result <- match failVar retType [expr] [([pat], innerExpr)] innerExpr
  return $ subst1 failVar (Builtin.Fail retType) result

matchCase
  :: AbstractM
  -> [(PatM, AbstractM)]
  -> AbstractM
  -> VIX ExprF
matchCase expr pats retType = do
  failVar <- forall "fail" retType
  result <- match failVar retType [expr] (first pure <$> pats) (pure failVar)
  return $ subst1 failVar (Builtin.Fail retType) result

matchClauses
  :: [AbstractM]
  -> [([PatM], AbstractM)]
  -> AbstractM
  -> VIX ExprF
matchClauses exprs pats retType = do
  failVar <- forall "fail" retType
  result <- match failVar retType exprs pats (pure failVar)
  return $ subst1 failVar (Builtin.Fail retType) result

type Match
  = MetaA -- ^ Failure variable
  -> ExprF -- ^ Return type
  -> [AbstractM] -- ^ Expressions to case on corresponding to the patterns in the clauses (usually variables)
  -> [Clause] -- ^ Clauses
  -> ExprF -- ^ The continuation for pattern match failure
  -> VIX ExprF

type NonEmptyMatch
  = MetaA -- ^ Failure variable
  -> ExprF -- ^ Return type
  -> [AbstractM] -- ^ Expressions to case on corresponding to the patterns in the clauses (usually variables)
  -> NonEmpty Clause -- ^ Clauses
  -> ExprF -- ^ The continuation for pattern match failure
  -> VIX ExprF

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

matchCon :: AbstractM -> NonEmptyMatch
matchCon expr failVar retType exprs clauses expr0 = do
  let (QConstr typeName _) = firstCon $ NonEmpty.head clauses
  cs <- constructors typeName

  cbrs <- forM cs $ \c -> do
    let clausesStartingWithC = NonEmpty.filter ((== c) . firstCon) clauses
    -- TODO Is there a nicer way to do this?
    params <- case clausesStartingWithC of
      firstClause:_ -> return $ typeParams $ firstPattern firstClause
      [] -> do
        typ <- typeOfM expr
        typ' <- whnf typ
        let (_, params) = appsView typ'
        return $ Vector.fromList params
    (ps, ys) <- conPatArgs c params

    let exprs' = (pure <$> Vector.toList ys) ++ exprs
    rest <- match failVar retType exprs' (decon clausesStartingWithC) (pure failVar)
    restScope <- abstractM (teleAbstraction ys) rest
    tele <- patternTelescope ys ps
    return $ ConBranch c tele restScope

  return $ fatBar failVar (Case expr (ConBranches cbrs) retType) expr0
  where
    firstCon (c:_, _) = constr c
    firstCon _ = error "firstCon "
    typeParams (ConPat _ ps _) = ps
    typeParams _ = error "match typeParams"
    constr (ConPat c _ _) = c
    constr _ = error "match constr"
    constructors typeName = do
      (DataDefinition (DataDef cs) _, _) <- definition typeName
      return $ QConstr typeName . constrName <$> cs

conPatArgs
  :: QConstr
  -> Vector (Plicitness, AbstractM)
  -> VIX (Vector (Plicitness, PatM, AbstractM), Vector MetaA)
conPatArgs c params = do
  ctype <- qconstructor c
  let (tele, _) = pisView (ctype :: AbstractM)
      tele' = instantiatePrefix (snd <$> params) tele
  vs <- forTeleWithPrefixM tele' $ \h _ s vs ->
    forall h $ instantiateTele pure vs s
  let ps = (\(p, v) -> (p, VarPat (metaHint v) v, metaType v))
        <$> Vector.zip (teleAnnotations tele') vs
  return (ps, vs)

patternTelescope
  :: Vector MetaA
  -> Vector (a, Pat typ b, AbstractM)
  -> VIX (Telescope a Expr MetaA)
patternTelescope ys ps = Telescope <$> mapM go ps
  where
    go (p, pat, e) = do
      s <- abstractM (teleAbstraction ys) e
      return $ TeleArg (patternHint pat) p s

matchLit :: AbstractM -> NonEmptyMatch
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

matchVar :: AbstractM -> NonEmptyMatch
matchVar expr failVar retType exprs clauses expr0 = do
  clauses' <- traverse go clauses
  match failVar retType exprs (NonEmpty.toList clauses') expr0
  where
    go :: Clause -> VIX Clause
    go (VarPat _ y:ps, e) = do
      ps' <- forM ps $ flip bitraverse pure $ \t -> do
        t' <- zonk t
        return $ subst1 y expr t'
      e' <- zonk e
      return (ps', subst1 y expr e')
    go _ = error "match var"

matchView :: AbstractM -> NonEmptyMatch
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
