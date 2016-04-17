{-# LANGUAGE FlexibleContexts, OverloadedStrings, ViewPatterns #-}
module Restrict where

import qualified Bound.Scope.Simple as Simple
import Data.Hashable
import Data.Maybe
import Data.Monoid
import qualified Data.Vector as Vector

import Syntax
import qualified Syntax.Lambda as Lambda
import qualified Syntax.Lifted as Lifted
import Meta
import TCM
import Util

restrictExpr
  :: (Eq v, Hashable v, Show v)
  => Lambda.Expr v
  -> TCM s (Lifted.LBody v)
restrictExpr expr = do
  trp "restrictExpr" $ show <$> expr
  modifyIndent succ
  result <- case expr of
    Lambda.Var v -> return $ Lifted.constantLBody $ pure v
    Lambda.Global n -> return $ Lifted.constantLBody $ Lifted.Operand $ Lifted.Global n
    Lambda.Lit l -> return $ Lifted.constantLBody $ Lifted.Operand $ Lifted.Lit l
    Lambda.Case e brs -> Lifted.caseLBody <$> restrictExpr e <*> restrictBranches brs
    (bindingsViewM lamView -> Just (tele, s)) -> Lifted.lamLBody (teleNames tele) <$> restrictScope s
    (appsView -> (Lambda.Con qc, Vector.fromList -> pes)) -> Lifted.conLBody qc =<< mapM restrictExpr (snd <$> pes)
    (appsView -> (e, Vector.fromList -> pes)) -> Lifted.callLBody <$> restrictExpr e <*> mapM restrictExpr (snd <$> pes)
  modifyIndent pred
  trp "restrictExpr res: " $ show <$> result
  return result
  where
    restrictBranches (ConBranches cbrs _) = Lifted.conLBodyBranches
      <$> sequence [(,,) c <$> restrictTele tele <*> restrictScope s | (c, tele, s) <- cbrs]
      <*> pure (Lifted.Operand $ Lifted.Lit 0)
    restrictBranches (LitBranches lbrs def) = Lifted.litLBodyBranches
      <$> sequence [(,) l <$> restrictExpr e | (l, e) <- lbrs]
      <*> restrictExpr def
    restrictTele = mapM (\(h, a, s) -> (,,) h a <$> restrictScope s) . unTelescope
    restrictScope = restrictExpr . fromScope

liftProgram :: [(Name, Lifted.LBody v)] -> [(Name, Lifted.Body Lifted.Expr v)]
liftProgram xs = xs >>= uncurry liftBody

liftBody :: Name -> Lifted.LBody v -> [(Name, Lifted.Body Lifted.Expr v)]
liftBody x (Lifted.Lifted liftedBodies body)
  = (x, inst $ Simple.fromScope body)
  : [ (inventName n, inst $ B <$> b)
    | (n, (_, b)) <- zip [0..] $ Vector.toList liftedBodies
    ]
  where
    inst = Lifted.instantiateBody (Lifted.Operand . Lifted.Global . inventName)
    inventName (Tele tele) = x <> fromMaybe "" hint <> shower tele
      where Hint hint = fst $ liftedBodies Vector.! tele
