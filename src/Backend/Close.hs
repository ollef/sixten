{-# LANGUAGE ViewPatterns #-}
module Backend.Close where

import Control.Monad.Except
import qualified Data.HashSet as HashSet
import Data.Monoid
import qualified Data.Vector as Vector

import Meta
import Syntax
import qualified Syntax.Sized.Closed as Closed
import qualified Syntax.Sized.SLambda as SLambda
import TCM
import TopoSort
import Util

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
  SLambda.Let h e t scope -> do
    t' <- closeExpr t
    e' <- closeExpr e
    x <- forall h t'
    let body = instantiate1 (pure x) scope
    closedBody <- closeExpr body
    let scope' = abstract1 x closedBody
    return $ Closed.Let h (Closed.Anno e' t') scope'
  SLambda.Case e brs -> Closed.Case <$> closeExpr e <*> closeBranches brs
  SLambda.Anno e t -> Closed.Anno <$> closeExpr e <*> closeExpr t
  (bindingsViewM SLambda.lamView -> Just (tele, s)) -> closeLambda tele s
  SLambda.Lam {} -> throwError "closeExpr Lam"

closeLambda
  :: Telescope () SLambda.Expr Meta
  -> Scope Tele SLambda.Expr Meta
  -> TCM CExprM
closeLambda tele lamScope = do
  sortedFvs <- do
    let fvs = toHashSet tele <> toHashSet lamScope

    deps <- forM (HashSet.toList fvs) $ \x -> do
      ds <- foldMapM HashSet.singleton $ metaType x
      return (x, ds)

    return $ Vector.fromList $ impure <$> topoSort deps

  vs <- forTeleWithPrefixM tele $ \h () s vs -> do
    let e = instantiateTele pure vs s
    e' <- closeExpr e
    forall h e'

  let lamExpr = instantiateTele pure vs lamScope
      vs' = sortedFvs <> vs
      abstr = teleAbstraction vs'
      tele'' = Telescope $ (\v -> (metaHint v, (), abstract abstr $ metaType v)) <$> vs'

  lamExpr' <- closeExpr lamExpr
  let lamScope' = abstract abstr lamExpr'

  voidedTele <- traverse (const $ throwError "closeLambda") tele''
  voidedLamScope <- traverse (const $ throwError "closeLambda") lamScope'

  let args = (\v -> Closed.Anno (pure v) (metaType v)) <$> sortedFvs

  return $ if null args
    then Closed.Lams voidedTele voidedLamScope
    else Closed.Call (Closed.Lams voidedTele voidedLamScope) args
  where
    impure [a] = a
    impure _ = error "closeLambda"

closeBranches :: BrsM SLambda.Expr -> TCM (BrsM Closed.Expr)
closeBranches (ConBranches cbrs) = fmap ConBranches $
  forM cbrs $ \(qc, tele, brScope) -> do
    vs <- forTeleWithPrefixM tele $ \h () s vs -> do
      let e = instantiateTele pure vs s
      e' <- closeExpr e
      forall h e'
    let brExpr = instantiateTele pure vs brScope
        abstr = teleAbstraction vs
        tele'' = Telescope $ (\v -> (metaHint v, (), abstract abstr $ metaType v)) <$> vs
    brExpr' <- closeExpr brExpr
    let brScope' = abstract abstr brExpr'
    return (qc, tele'', brScope')
closeBranches (LitBranches lbrs def) = LitBranches
  <$> mapM (\(l, e) -> (,) l <$> closeExpr e) lbrs <*> closeExpr def
closeBranches (NoBranches sz) = NoBranches <$> closeExpr sz
