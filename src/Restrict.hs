{-# LANGUAGE FlexibleContexts, ViewPatterns #-}
module Restrict where

import Data.Hashable
import qualified Data.Vector as Vector

import Syntax
import qualified Syntax.Lambda as Lambda
import qualified Syntax.Lifted as Lifted
import TCM

restrictExpr
  :: (Eq v, Hashable v, Show v)
  => Lambda.Expr v
  -> TCM s (Lifted.LBody v)
restrictExpr expr = case expr of
  Lambda.Var v -> return $ Lifted.constant $ pure v
  Lambda.Global n -> return $ Lifted.constant $ Lifted.Operand $ Lifted.Global n
  Lambda.Lit l -> return $ Lifted.constant $ Lifted.Operand $ Lifted.Lit l
  Lambda.Case e brs -> Lifted.case_ <$> restrictExpr e <*> restrictBranches brs
  (bindingsViewM lamView -> Just (tele, s)) -> Lifted.lam (teleNames tele) <$> restrictScope s
  (appsView -> (Lambda.Con qc, Vector.fromList -> pes)) -> Lifted.con qc =<< mapM restrictExpr (snd <$> pes)
  (appsView -> (e, Vector.fromList -> pes)) -> Lifted.call <$> restrictExpr e <*> mapM restrictExpr (snd <$> pes)
  where
    restrictBranches (ConBranches cbrs _) = Lifted.conBranches
      <$> sequence [(,,) c <$> restrictTele tele <*> restrictScope s | (c, tele, s) <- cbrs]
      <*> pure (Lifted.Operand $ Lifted.Lit 0)
    restrictBranches (LitBranches lbrs def) = Lifted.litBranches
      <$> sequence [(,) l <$> restrictExpr e | (l, e) <- lbrs]
      <*> restrictExpr def
    restrictTele = mapM (\(h, a, s) -> (,,) h a <$> restrictScope s) . unTelescope
    restrictScope = restrictExpr . fromScope
