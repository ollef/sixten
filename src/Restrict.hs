{-# LANGUAGE FlexibleContexts, ViewPatterns #-}
module Restrict where

import Control.Monad.Except
import Data.Hashable
import qualified Data.Vector as Vector

import Context
import Syntax
import qualified Syntax.Lambda as Lambda
import qualified Syntax.LL as LL

restrictExpr
  :: (MonadError String cxt, Context cxt, Eq v, Hashable v, Show v)
  => Lambda.Expr v
  -> cxt (LL.LBody v)
restrictExpr expr = {- trace "restrict" $ -} case expr of
  Lambda.Var v -> return $ LL.constantLifted $ pure v
  Lambda.Global n -> return $ LL.constantLifted $ LL.Operand $ LL.Global n
  Lambda.Lit l -> return $ LL.constantLifted $ LL.Operand $ LL.Lit l
  Lambda.Case e brs -> LL.caseLifted <$> restrictExpr e <*> restrictBranches brs
  (bindingsViewM Lambda.lamView -> Just (tele, s)) -> LL.lamLifted (teleNames tele) <$> restrictScope s
  (Lambda.appsView -> (Lambda.Con qc, Vector.fromList -> es)) -> LL.conLifted qc =<< mapM restrictExpr es
  (Lambda.appsView -> (e, Vector.fromList -> es)) -> LL.callLifted <$> restrictExpr e <*> mapM restrictExpr es
  where
    restrictBranches (ConBranches cbrs _) = LL.conBranchesLifted
      <$> sequence [(,,) c vs <$> restrictScope s | (c, vs, s) <- cbrs]
      <*> pure (LL.Operand $ LL.Lit 0)
    restrictBranches (LitBranches lbrs def) = LL.litBranchesLifted
      <$> sequence [(,) l <$> restrictExpr e | (l, e) <- lbrs]
      <*> restrictExpr def
    restrictScope = restrictExpr . fromScope
