{-# LANGUAGE ScopedTypeVariables #-}
module Inference.Match where

import Control.Monad.Except
import Data.Bifoldable
import Data.Bifunctor
import Data.Foldable
import Data.Function
import Data.List.NonEmpty(NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Monoid
import qualified Data.Vector as Vector
import Data.Vector(Vector)

import qualified Builtin
import Inference.Normalise
import Inference.TypeOf
import Meta
import Syntax
import Syntax.Abstract
import Syntax.Abstract.Pattern
import VIX
import Util

type PatM = Pat AbstractM MetaA
type Clause =
  ( [PatM]
  , Expr (Var Fail MetaA)
  )

data Fail = Fail

fatBar :: Expr (Var Fail v) -> Expr (Var Fail v) -> Expr (Var Fail v)
fatBar e e' = case foldMap (bifoldMap (:[]) mempty) e of
  [] -> e
  [_] -> e >>= unvar (\Fail -> e') (pure . F)
  _ -> Let mempty (Lam mempty Explicit (Global Builtin.UnitName) $ abstractNone e')
    $ instantiateSome (\Fail -> App (pure $ B ()) Explicit (Con Builtin.Unit))
    $ F <$> toScope e

matchSingle
  :: AbstractM
  -> PatM
  -> AbstractM
  -> VIX (Expr (Var Fail MetaA))
matchSingle expr pat innerExpr
  = match [expr] [([pat], F <$> innerExpr)] $ F <$> innerExpr

matchCase
  :: AbstractM
  -> [(PatM, AbstractM)]
  -> VIX (Expr (Var Fail MetaA))
matchCase expr pats
  = match [expr] (bimap pure (fmap F) <$> pats) (pure $ B Fail)

matchClauses
  :: [AbstractM]
  -> [([PatM], AbstractM)]
  -> VIX (Expr (Var Fail MetaA))
matchClauses exprs pats
  = match exprs (fmap (fmap F) <$> pats) (pure $ B Fail)

type Match
  = [AbstractM] -- ^ Expressions to case on corresponding to the patterns in the clauses (usually variables)
  -> [Clause] -- ^ Clauses
  -> Expr (Var Fail MetaA) -- ^ The continuation for pattern match failure
  -> VIX (Expr (Var Fail MetaA))

type NonEmptyMatch
  = [AbstractM] -- ^ Expressions to case on corresponding to the patterns in the clauses (usually variables)
  -> NonEmpty Clause -- ^ Clauses
  -> Expr (Var Fail MetaA) -- ^ The continuation for pattern match failure
  -> VIX (Expr (Var Fail MetaA))

-- | Desugar pattern matching clauses
match :: Match
match _ [] expr0 = return expr0
match [] clauses expr0 = return $ foldr go expr0 clauses
  where
    go :: Clause -> Expr (Var Fail MetaA) -> Expr (Var Fail MetaA)
    go ([], s) x = fatBar s x
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
    (ps, ys) <- conPatArgs c =<< typeOfM expr

    let exprs' = (pure <$> Vector.toList ys) ++ exprs
    rest <- match exprs' (decon clausesStartingWithC) (pure $ B Fail)
    rest' <- fromScope <$> zonkBound (toScope rest)
    let restScope = abstract (unvar (\Fail -> Nothing) $ teleAbstraction ys) rest'
    tele <- patternTelescope ys ps
    return (c, F <$> tele, restScope)

  cbrs' <- maybe
    (throwError "matchCon: empty branches")
    return
    (NonEmpty.nonEmpty cbrs)

  return $ fatBar (Case (F <$> expr) (ConBranches cbrs')) expr0
  where
    firstCon = constr . firstPattern
    constr (ConPat c _ _) = c
    constr _ = error "match constr"
    constructors typeName = do
      (DataDefinition (DataDef cs) _, _ :: Expr ()) <- definition typeName
      return $ QConstr typeName . constrName <$> cs

conPatArgs
  :: QConstr
  -> AbstractM
  -> VIX (Vector (Plicitness, PatM, AbstractM), Vector MetaA)
conPatArgs c typ = do
  typ' <- whnf typ
  let (_, args) = appsView typ'
  ctype <- qconstructor c
  let (tele, _) = pisView (ctype :: AbstractM)
      tele' = instantiatePrefix (snd <$> Vector.fromList args) tele
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
      e' <- zonk e
      return (patternHint pat, p, abstract (teleAbstraction ys) e')

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
    unpat (ConPat _ _ pats) = Vector.toList $ snd3 <$> pats
    unpat (LitPat _) = mempty
    unpat _ = error "match unpat"
