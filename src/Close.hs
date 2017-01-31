{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RecursiveDo, TypeFamilies, ViewPatterns #-}
module Close where

import Control.Monad.Except
import qualified Data.HashSet as HashSet
import Data.Monoid
import qualified Data.Vector as Vector

import Meta
import Syntax
import qualified Syntax.SLambda as SLambda
import qualified Syntax.Closed as Closed
import TCM
import TopoSort

type Meta = MetaVar Closed.Expr
type ExprM = SLambda.Expr Meta
type CExprM = Closed.Expr Meta

type BrsM e = Branches QConstr () e Meta

closeExpr :: ExprM -> TCM CExprM
closeExpr expr = case expr of
  SLambda.Var v -> return $ Closed.Var v
  SLambda.Global g -> return $ Closed.Global g
  SLambda.Lit l -> return $ Closed.Lit l
  SLambda.Con qc es -> Closed.Con qc <$> mapM closeExpr es
  SLambda.App e1 e2 -> Closed.apps <$> closeExpr e1 <*> (pure <$> closeExpr e2)
  SLambda.Case e brs -> Closed.Case <$> closeExpr e <*> closeBranches brs
  SLambda.Sized sz e -> Closed.Sized <$> closeExpr sz <*> closeExpr e
  (bindingsViewM SLambda.lamView -> Just (tele, s)) -> closeLambda tele s
  SLambda.Lam {} -> throwError "closeExpr Lam"

closeLambda
  :: Telescope () SLambda.Expr Meta
  -> Scope Tele SLambda.Expr Meta
  -> TCM CExprM
closeLambda tele lamScope = mdo
  sortedFvs <- do
    -- TODO move into util function
    -- TODO do we need to use foldMapM here?
    teleFvs <- foldMapM (:[]) tele
    scopeFvs <- foldMapM (:[]) lamScope
    let fvs = HashSet.fromList teleFvs <> HashSet.fromList scopeFvs

    deps <- forM (HashSet.toList fvs) $ \x -> do
      ds <- foldMapM HashSet.singleton $ metaType x
      return (x, ds)

    return $ Vector.fromList $ impure <$> topoSort deps

  vs <- forMTele tele $ \h () s -> do
    let e = instantiateTele pure vs s
    e' <- closeExpr e
    forall h () e'

  let lamExpr = instantiateTele pure vs lamScope
      vs' = sortedFvs <> vs
      abstr = teleAbstraction vs'
      tele'' = Telescope $ (\v -> (metaHint v, (), abstract abstr $ metaType v)) <$> vs'

  lamExpr' <- closeExpr lamExpr
  let lamScope' = abstract abstr lamExpr'

  voidedTele <- traverse (const $ throwError "closeLambda") tele''
  voidedLamScope <- traverse (const $ throwError "closeLambda") lamScope'

  let args = (\v -> Closed.Sized (metaType v) $ Closed.Var v) <$> sortedFvs

  return $ if null args
    then Closed.Lams voidedTele voidedLamScope
    else Closed.Call (Closed.Lams voidedTele voidedLamScope) args
  where
    impure [a] = a
    impure _ = error "closeLambda"

closeBranches :: BrsM SLambda.Expr -> TCM (BrsM Closed.Expr)
closeBranches (ConBranches cbrs) = fmap ConBranches $
  forM cbrs $ \(qc, tele, brScope) -> mdo
    vs <- forMTele tele $ \h () s -> do
      let e = instantiateTele pure vs s
      e' <- closeExpr e
      forall h () e'
    let brExpr = instantiateTele pure vs brScope
        abstr = teleAbstraction vs
        tele'' = Telescope $ (\v -> (metaHint v, (), abstract abstr $ metaType v)) <$> vs
    brExpr' <- closeExpr brExpr
    let brScope' = abstract abstr brExpr'
    return (qc, tele'', brScope')
closeBranches (LitBranches lbrs def) = LitBranches
  <$> mapM (\(l, e) -> (,) l <$> closeExpr e) lbrs <*> closeExpr def
closeBranches (NoBranches sz) = NoBranches <$> closeExpr sz
