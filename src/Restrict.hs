{-# LANGUAGE FlexibleContexts, ViewPatterns #-}
module Restrict where

import Data.Hashable
import qualified Data.Vector as Vector

import Syntax
import qualified Syntax.Lambda as Lambda
import qualified Syntax.LL as LL
import TCM

restrictExpr
  :: (Eq v, Hashable v, Show v)
  => Lambda.Expr v
  -> TCM s (LL.LBody v)
restrictExpr expr = case expr of
  Lambda.Var v -> return $ LL.constantLifted $ pure v
  Lambda.Global n -> return $ LL.constantLifted $ LL.Operand $ LL.Global n
  Lambda.Lit l -> return $ LL.constantLifted $ LL.Operand $ LL.Lit l
  Lambda.Case e brs -> LL.caseLifted <$> restrictExpr e <*> restrictBranches brs
  (bindingsViewM lamView -> Just (tele, s)) -> LL.lamLifted (teleNames tele) <$> restrictScope s
  (appsView -> (Lambda.Con qc, Vector.fromList -> pes)) -> LL.conLifted qc =<< mapM restrictExpr (snd <$> pes)
  (appsView -> (e, Vector.fromList -> pes)) -> LL.callLifted <$> restrictExpr e <*> mapM restrictExpr (snd <$> pes)
  where
    restrictBranches (ConBranches cbrs _) = LL.conBranchesLifted
      <$> sequence [(,,) c <$> restrictTele tele <*> restrictScope s | (c, tele, s) <- cbrs]
      <*> pure (LL.Operand $ LL.Lit 0)
    restrictBranches (LitBranches lbrs def) = LL.litBranchesLifted
      <$> sequence [(,) l <$> restrictExpr e | (l, e) <- lbrs]
      <*> restrictExpr def
    restrictTele = mapM (\(h, a, s) -> (,,) h a <$> restrictScope s) . unTelescope
    restrictScope = restrictExpr . fromScope
