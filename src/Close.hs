{-# LANGUAGE OverloadedStrings, RecursiveDo, ViewPatterns #-}
module Close where

import qualified Bound.Scope.Simple as Simple
import Control.Monad.Except
import qualified Data.HashSet as HS
import Data.Monoid
import qualified Data.Vector as Vector

import Meta
import Syntax
import qualified Syntax.SLambda as SLambda
import qualified Syntax.Closed as Closed
import TCM
import TopoSort
import Util

type Meta = MetaVar Closed.Expr
type ExprM = SLambda.Expr Meta
type CExprM = Closed.Expr Meta

type SExprM = SLambda.SExpr Meta
type CSExprM = Closed.SExpr Meta

type BrsM e = SimpleBranches QConstr e Meta

closeExpr :: ExprM -> TCM CExprM
closeExpr expr = case expr of
  SLambda.Var v -> return $ Closed.Var v
  SLambda.Global g -> return $ Closed.Global g
  SLambda.Lit l -> return $ Closed.Lit l
  SLambda.Con qc es -> Closed.Con qc <$> mapM closeSExpr es
  (simpleBindingsViewM SLambda.lamView . SLambda.Sized (SLambda.Global "impossible") -> Just (tele, s)) -> closeLambda tele s
  SLambda.Lam {} -> throwError "Lambda2Lambda Lam"
  SLambda.Case e brs -> Closed.Case <$> closeSExpr e <*> closeBranches brs
  (SLambda.appsView -> (e, es)) -> Closed.apps <$> closeExpr e <*> mapM closeSExpr es

closeLambda
  :: Telescope Simple.Scope () SLambda.Expr Meta
  -> Simple.Scope Tele SLambda.SExpr Meta
  -> TCM CExprM
closeLambda tele lamScope = mdo
  sortedFvs <- do
    -- TODO move into util function
    teleFvs <- foldMapM (:[]) tele
    scopeFvs <- foldMapM (:[]) lamScope
    let fvs = HS.fromList teleFvs <> HS.fromList scopeFvs

    deps <- forM (HS.toList fvs) $ \x -> do
      ds <- foldMapM HS.singleton $ metaType x
      return (x, ds)

    return $ Vector.fromList $ impure <$> topoSort deps

  vs <- forMTele tele $ \h () s -> do
    let e = instantiateVar ((vs Vector.!) . unTele) s
    e' <- closeExpr e
    forall_ h e'

  let lamExpr = instantiateVar ((vs Vector.!) . unTele) lamScope
      vs' = sortedFvs <> vs
      abstr = teleAbstraction vs'
      tele'' = Telescope $ (\v -> (metaHint v, (), Simple.abstract abstr $ metaType v)) <$> vs'

  lamExpr' <- closeSExpr lamExpr
  let lamScope' = Simple.abstract abstr lamExpr'

  voidedTele <- traverse (const $ throwError "closeLambda") tele''
  voidedLamScope <- traverse (const $ throwError "closeLambda") lamScope'

  let args = (\v -> Closed.Sized (metaType v) $ Closed.Var v) <$> sortedFvs

  return $ if null args
    then Closed.Lams voidedTele voidedLamScope
    else Closed.Call (Closed.Lams voidedTele voidedLamScope) args
  where
    impure [a] = a
    impure _ = error "closeLambda"

closeSExpr :: SExprM -> TCM CSExprM
closeSExpr (SLambda.Sized sz e) = Closed.Sized <$> closeExpr sz <*> closeExpr e

closeBranches :: BrsM SLambda.Expr -> TCM (BrsM Closed.Expr)
closeBranches (SimpleConBranches cbrs) = fmap SimpleConBranches $
  forM cbrs $ \(qc, tele, brScope) -> mdo
    vs <- forMTele tele $ \h () s -> do
      let e = instantiateVar ((vs Vector.!) . unTele) s
      e' <- closeExpr e
      forall_ h e'
    let brExpr = instantiateVar ((vs Vector.!) . unTele) brScope
        abstr = teleAbstraction vs
        tele'' = Telescope $ (\v -> (metaHint v, (), Simple.abstract abstr $ metaType v)) <$> vs
    brExpr' <- closeExpr brExpr
    let brScope' = Simple.abstract abstr brExpr'
    return (qc, tele'', brScope')
closeBranches (SimpleLitBranches lbrs def) = SimpleLitBranches
  <$> mapM (\(l, e) -> (,) l <$> closeExpr e) lbrs <*> closeExpr def
