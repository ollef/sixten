{-# LANGUAGE OverloadedStrings, RecursiveDo, ViewPatterns #-}
module Lift where

import qualified Bound.Scope.Simple as Simple
import Control.Monad.Except
import Data.Bifunctor
import qualified Data.HashSet as HS
import Data.Monoid
import qualified Data.Vector as Vector

import Meta
import Syntax
import qualified Syntax.SLambda as SLambda
import qualified Syntax.Lifted as Lifted
import TCM
import TopoSort
import Util

type Meta = MetaVar SLambda.Expr
type ExprM s = SLambda.Expr (Meta s)
type LExprM s = Lifted.Expr (Meta s)

type SExprM s = SLambda.SExpr (Meta s)
type SLExprM s = Lifted.SExpr (Meta s)

type BrsM e s = SimpleBranches QConstr e (Meta s)

liftExpr :: ExprM s -> TCM s (LExprM s)
liftExpr expr = case expr of
  SLambda.Var v -> return $ Lifted.Var v
  SLambda.Global g -> return $ Lifted.Global g
  SLambda.Lit l -> return $ Lifted.Lit l
  SLambda.Con qc es -> Lifted.Con qc <$> mapM liftSExpr es
  (simpleBindingsViewM SLambda.lamView . SLambda.Sized (SLambda.Global "impossible") -> Just (tele, s)) -> liftLambda tele s
  SLambda.Lam {} -> throwError "Lambda2Lambda Lam"
  SLambda.Case e brs -> Lifted.Case <$> liftSExpr e <*> liftBranches brs
  (SLambda.appsView -> (e, es)) -> Lifted.apps <$> liftExpr e <*> mapM liftSExpr es

liftLambda
  :: SimpleTelescope SLambda.Expr (Meta s)
  -> Simple.Scope Tele SLambda.SExpr (Meta s)
  -> TCM s (LExprM s)
liftLambda tele lamScope = mdo
  sortedFvs <- do
    -- TODO move into util function
    teleFvs <- foldMapM (:[]) tele
    scopeFvs <- foldMapM (:[]) lamScope
    let fvs = HS.fromList teleFvs <> HS.fromList scopeFvs

    deps <- forM (HS.toList fvs) $ \x -> do
      ds <- foldMapM HS.singleton $ metaType x
      return (x, ds)

    return $ Vector.fromList $ impure <$> topoSort deps

  tele' <- forMSimpleTele tele $ \h s -> do
    let e = instantiateVar ((vs Vector.!) . unTele) s
    v <- forall_ h e
    e' <- liftExpr e
    return (v, e')

  let vs = fst <$> tele'
      lamExpr = instantiateVar ((vs Vector.!) . unTele) lamScope
      vs' = sortedFvs <> vs
      abstr = teleAbstraction vs'
      tele'' = SimpleTelescope $ bimap metaHint (Simple.abstract abstr) <$> tele'

  lamExpr' <- liftSExpr lamExpr
  let lamScope' = Simple.abstract abstr lamExpr'

  voidedTele <- traverse (const $ throwError "liftLambda") tele''
  voidedLamScope <- traverse (const $ throwError "liftLambda") lamScope'

  args <- forM sortedFvs $ \m -> do
    sz <- liftExpr $ metaType m
    return $ Lifted.Sized sz $ Lifted.Var m

  return $ if null args
    then Lifted.Lams voidedTele voidedLamScope
    else Lifted.Call (Lifted.Lams voidedTele voidedLamScope) args
  where
    impure [a] = a
    impure _ = error "liftLambda"


liftSExpr :: SExprM s -> TCM s (SLExprM s)
liftSExpr (SLambda.Sized sz e) = Lifted.Sized <$> liftExpr sz <*> liftExpr e

liftBranches :: BrsM SLambda.Expr s -> TCM s (BrsM Lifted.Expr s)
liftBranches (SimpleConBranches cbrs) = fmap SimpleConBranches $
  forM cbrs $ \(qc, tele, brScope) -> mdo
    tele' <- forMSimpleTele tele $ \h s -> do
      let e = instantiateVar ((vs Vector.!) . unTele) s
      v <- forall_ h e
      e' <- liftExpr e
      return (v, e')
    let vs = fst <$> tele'
        brExpr = instantiateVar ((vs Vector.!) . unTele) brScope
        abstr = teleAbstraction vs
        tele'' = SimpleTelescope $ bimap metaHint (Simple.abstract abstr) <$> tele'
    brExpr' <- liftExpr brExpr
    let brScope' = Simple.abstract abstr brExpr'
    return (qc, tele'', brScope')
liftBranches (SimpleLitBranches lbrs def) = SimpleLitBranches
  <$> mapM (\(l, e) -> (,) l <$> liftExpr e) lbrs <*> liftExpr def
