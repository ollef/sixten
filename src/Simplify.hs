{-# LANGUAGE RecursiveDo #-}
module Simplify where

import Bound
import Meta
import Syntax
import Syntax.Abstract
import TCM

simplifyExpr :: AbstractM -> TCM AbstractM
simplifyExpr expr = case expr of
  Var _       -> return expr
  Global _    -> return expr
  Con _       -> return expr
  Lit _       -> return expr
  Pi h a t s -> do
    t' <- simplifyExpr t
    Pi h a t' <$> simplifyScope h t' s
  Lam h a t s -> do
    t' <- simplifyExpr t
    etaLam h a t' <$> simplifyScope h t' s
  App e1 p e2 -> betaApp <$> simplifyExpr e1 <*> pure p <*> simplifyExpr e2
  -- TODO do something clever here
  Case e brs  -> Case <$> simplifyExpr e <*> simplifyBranches brs
  where
    simplifyScope h t s = do
      x <- forall h t
      e' <- simplifyExpr $ instantiate1 (pure x) s
      return $ abstract1 x e'

simplifyBranches
  :: BranchesM QConstr Expr
  -> TCM (BranchesM QConstr Expr)
simplifyBranches (ConBranches cbrs typ) = ConBranches
  <$> sequence
    [ mdo
      vs <- forMTele tele $ \h _ -> forall h . instantiateTele pureVs
      let pureVs = pure <$> vs
      e' <- simplifyExpr $ instantiateTele pureVs s
      let s' = abstract (teleAbstraction vs) e'
      return (c, tele, s')
    | (c, tele, s) <- cbrs]
  <*> pure typ
simplifyBranches (LitBranches lbrs def) = LitBranches
  <$> sequence [(,) l <$> simplifyExpr e | (l, e) <- lbrs]
  <*> simplifyExpr def

simplifyDef
  :: Definition Expr (MetaVar Expr)
  -> TCM (Definition Expr (MetaVar Expr))
simplifyDef (Definition e) = Definition <$> simplifyExpr e
simplifyDef def@(DataDefinition _) = return def
