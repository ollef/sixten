{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, MonadComprehensions, ScopedTypeVariables #-}
module Match where

import Control.Monad.Except
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import Data.Function
import Data.List.NonEmpty(NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Monoid
import qualified Data.Vector as Vector
import Data.Vector(Vector)

import Builtin
import Match.Pattern
import Meta
import Syntax
import Syntax.Abstract
import TCM
import Util

type PatM = Pat AbstractM MetaP
type Clause =
  ( [PatM]
  , ExprP (Var Fail MetaP)
  )

data Fail = Fail

fatBar :: a -> Expr a (Var Fail v) -> Expr a (Var Fail v) -> Expr a (Var Fail v)
fatBar p e e' = case foldMap (bifoldMap (:[]) mempty) e of
  [] -> e
  [_] -> e >>= unvar (\Fail -> e') (pure . F)
  _ -> Let mempty (Lam mempty p (Global UnitName) $ abstractNone e')
    $ instantiateSome (\Fail -> App (pure $ B ()) p (Con Builtin.Unit))
    $ F <$> toScope e

matchSingle
  :: AbstractM
  -> PatM
  -> AbstractM
  -> TCM AbstractM
matchSingle expr pat innerExpr = do
  result <- match [expr] [([pat], F <$> innerExpr)] $ F <$> innerExpr
  traverse (unvar (const $ throwError "matchSingle is not allowed to fail") pure) result

matchCase
  :: AbstractM
  -> [(PatM, AbstractM)]
  -> TCM AbstractM
matchCase expr pats = do
  result <- match [expr] (bimap pure (fmap F) <$> pats) (pure $ B Fail)
  traverse (unvar (const $ throwError "matchCase is not allowed to fail") pure) result

matchClauses
  :: [AbstractM]
  -> [([PatM], AbstractM)]
  -> TCM AbstractM
matchClauses exprs pats = do
  result <- match exprs (fmap (fmap F) <$> pats) (pure $ B Fail)
  traverse (unvar (const $ throwError "matchClauses is not allowed to fail") pure) result

type Match
  = [AbstractM] -- ^ Expressions to case on corresponding to the patterns in the clauses (usually variables)
  -> [Clause] -- ^ Clauses
  -> ExprP (Var Fail MetaP) -- ^ The continuation for pattern match failure
  -> TCM (ExprP (Var Fail MetaP))

type NonEmptyMatch
  = [AbstractM] -- ^ Expressions to case on corresponding to the patterns in the clauses (usually variables)
  -> NonEmpty Clause -- ^ Clauses
  -> ExprP (Var Fail MetaP) -- ^ The continuation for pattern match failure
  -> TCM (ExprP (Var Fail MetaP))

-- | Desugar pattern matching clauses
match :: Match
match _ [] expr0 = return expr0
match [] clauses expr0 = return $ foldr go expr0 clauses
  where
    go :: Clause -> ExprP (Var Fail MetaP) -> ExprP (Var Fail MetaP)
    go ([], s) x = fatBar Explicit s x
    go _ _ = error "match go"
match xs clauses expr0
  = foldrM
    (matchMix xs)
    expr0
  $ NonEmpty.groupBy ((==) `on` patternType . firstPattern) clauses

firstPattern :: ([c], b) -> c
firstPattern = head . fst

matchMix :: NonEmptyMatch
matchMix (expr:exprs) clauses@(clause NonEmpty.:| _) expr0
  = f expr exprs clauses expr0
  where
    f = case patternType $ firstPattern clause of
      VarPatType -> matchVar
      LitPatType -> matchLit
      ConPatType -> matchCon
      ViewPatType _ -> matchView
matchMix _ _ _ = error "matchMix"

matchCon :: AbstractM -> NonEmptyMatch
matchCon expr exprs clauses expr0 = do
  let (QConstr typeName _) = firstCon $ NonEmpty.head clauses
  cs <- constructors typeName

  cbrs <- forM cs $ \c -> do
    let clausesStartingWithC = NonEmpty.filter ((== c) . firstCon) clauses
        ConPat _ ps = firstPattern $ head clausesStartingWithC
    ys <- forM ps $ \(p, pat, typ) -> forall (patternHint pat) p typ
    let exprs' = (pure <$> Vector.toList ys) ++ exprs
    rest <- match exprs' (decon clausesStartingWithC) (pure $ B Fail)
    rest' <- fromScope <$> zonkBound (toScope rest)
    let restScope = abstract (unvar (\Fail -> Nothing) $ teleAbstraction ys) rest'
    return (c, F <$> patternTelescope ps, restScope)

  cbrs' <- maybe
    (throwError "matchCon: empty branches")
    return
    (NonEmpty.nonEmpty cbrs)

  return $ fatBar Explicit (Case (F <$> expr) (ConBranches cbrs')) expr0
  where
    firstCon = constr . firstPattern
    constr (ConPat c _) = c
    constr _ = error "match constr"
    constructors typeName = do
      (DataDefinition (DataDef cs), _ :: ExprP ()) <- definition typeName
      return $ QConstr typeName . constrName <$> cs

patternTelescope
  :: Vector (a, Pat typ b, Expr a v)
  -> Telescope a (Expr a) v
patternTelescope = Telescope . fmap go
  where
    go (p, pat, e) = (patternHint pat, p, abstractNone e) -- TODO abstract something?

matchLit :: AbstractM -> NonEmptyMatch
matchLit expr exprs clauses expr0 = do
  let ls = NonEmpty.nub $ (lit . firstPattern) <$> clauses
  lbrs <- forM ls $ \l -> do
    let clausesStartingWithL = NonEmpty.filter ((== LitPat l) . firstPattern) clauses
    rest <- match exprs (decon clausesStartingWithL) (pure $ B Fail)
    return (l, rest)
  return $ Case (F <$> expr) $ LitBranches lbrs expr0
  where
    lit (LitPat l) = l
    lit _ = error "match lit"

matchVar :: AbstractM -> NonEmptyMatch
matchVar expr exprs clauses
  = match exprs $ NonEmpty.toList $ go <$> clauses
  where
    go :: Clause -> Clause
    go (VarPat _ y:ps, s) = (ps, subst y (F <$> expr) s)
    go (WildcardPat:ps, s) = (ps, s)
    go _ = error "match var"
    subst v e e' = e' >>= unvar (pure . B) f
      where
        f i | i == v = e
            | otherwise = pure $ F i

matchView :: AbstractM -> NonEmptyMatch
matchView expr exprs clauses = match (App f Explicit expr : exprs) $ NonEmpty.toList $ deview <$> clauses
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
    unpat (ConPat _ pats) = Vector.toList $ snd3 <$> pats
    unpat (LitPat _) = mempty
    unpat _ = error "match unpat"
