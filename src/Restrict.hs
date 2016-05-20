{-# LANGUAGE FlexibleContexts, OverloadedStrings, ViewPatterns #-}
module Restrict where

import qualified Bound.Scope.Simple as Simple
import Data.Hashable
import Data.Maybe
import Data.Monoid

import Syntax
import qualified Syntax.Lambda as Lambda
import qualified Syntax.Lifted as Lifted
import Meta
import TCM
import Util
import qualified Data.Vector as Vector

restrictBody
  :: (Eq v, Hashable v, Show v)
  => Lambda.SExpr v
  -> TCM s (Lifted.LBody v)
restrictBody expr = case expr of
    (simpleBindingsViewM Lambda.lamView -> Just (tele, s)) ->
      Lifted.lamLBody (simpleTeleNames tele) <$> restrictSScope s
    _ -> Lifted.mapLifted Lifted.Constant <$> restrictSExpr expr

restrictSExpr
  :: (Eq v, Hashable v, Show v)
  => Lambda.SExpr v
  -> TCM s (Lifted.LExpr v)
restrictSExpr (Lambda.Sized sz expr) = do
  rsz <- restrictExpr sz $ Lifted.pureLifted
                         $ Lifted.Sized (Lifted.Lit 1)
                         $ Lifted.Operand $ Lifted.Lit 1
  restrictExpr expr rsz

restrictSExprSize
  :: (Eq v, Hashable v, Show v)
  => Lambda.SExpr v
  -> TCM s (Lifted.LExpr v, Lifted.LExpr v)
restrictSExprSize (Lambda.Sized sz expr) = do
  rsz <- restrictConstantSize sz 1
  rexpr <- restrictExpr expr rsz
  return (rexpr, rsz)

restrictConstantSize
  :: (Eq v, Hashable v, Show v)
  => Lambda.Expr v
  -> Literal
  -> TCM s (Lifted.LExpr v)
restrictConstantSize expr sz =
  restrictExpr expr $ Lifted.pureLifted
                    $ Lifted.Sized (Lifted.Lit 1)
                    $ Lifted.Operand $ Lifted.Lit sz

restrictExpr
  :: (Eq v, Hashable v, Show v)
  => Lambda.Expr v
  -> Lifted.LExpr v
  -> TCM s (Lifted.LExpr v)
restrictExpr expr sz = do
  trp "restrictExpr" $ show <$> expr
  modifyIndent succ
  result <- case expr of
    Lambda.Var v -> return $ Lifted.lSizedOperand sz $ Lifted.Local v
    Lambda.Global g -> return $ Lifted.lSizedOperand sz $ Lifted.Global g
    Lambda.Lit l -> return $ Lifted.lSizedOperand sz $ Lifted.Lit l
    Lambda.Case e brs -> Lifted.caseLExpr <$> restrictSExprSize e <*> restrictBranches brs
    Lambda.Con qc es -> Lifted.conLExpr sz qc <$> mapM restrictSExprSize es
    (simpleBindingsViewM Lambda.lamView . Lambda.Sized undefined -> Just (tele, s)) ->
      fmap Lifted.liftLBody $ Lifted.lamLBody (simpleTeleNames tele) <$> restrictSScope s
    (Lambda.appsView -> (e, es)) ->
      Lifted.callLExpr sz <$> restrictConstantSize e 1 <*> mapM restrictSExpr es
  modifyIndent pred
  trp "restrictExpr res: " $ show <$> result
  return result
  where
    restrictBranches (SimpleConBranches cbrs) = Lifted.conLExprBranches
      <$> sequence [(,,) c <$> restrictTele tele <*> restrictScope s sz | (c, tele, s) <- cbrs]
    restrictBranches (SimpleLitBranches lbrs def) = Lifted.litLExprBranches
      <$> sequence [(,) l <$> restrictExpr e sz | (l, e) <- lbrs]
      <*> restrictExpr def sz
    restrictTele = mapM (\(h, s) -> (,) h <$> restrictConstantSizeScope s 1)
                 . unSimpleTelescope

restrictScope
  :: (Eq b, Eq v, Show b, Show v, Hashable b, Hashable v)
  => Simple.Scope b Lambda.Expr v
  -> Lifted.LExpr v
  -> TCM s (Simple.Scope b Lifted.LExpr v)
restrictScope expr sz
  = Simple.toScope <$> restrictExpr (Simple.fromScope expr) (F <$> sz)

restrictSScope
  :: (Eq b, Eq v, Show b, Show v, Hashable b, Hashable v)
  => Simple.Scope b Lambda.SExpr v
  -> TCM s (Simple.Scope b Lifted.LExpr v)
restrictSScope s = Simple.toScope <$> restrictSExpr (Simple.fromScope s)

restrictConstantSizeScope
  :: (Eq b, Eq v, Show b, Show v, Hashable b, Hashable v)
  => Simple.Scope b Lambda.Expr v
  -> Literal
  -> TCM s (Simple.Scope b Lifted.LExpr v)
restrictConstantSizeScope expr sz
  = Simple.toScope <$> restrictConstantSize (Simple.fromScope expr) sz

liftProgram :: [(Name, Lifted.LBody v)] -> [(Name, Lifted.Body v)]
liftProgram xs = xs >>= uncurry liftBody

liftBody :: Name -> Lifted.LBody v -> [(Name, Lifted.Body v)]
liftBody x (Lifted.Lifted liftedBodies (Simple.Scope body))
  = (x, inst body)
  : [ (inventName n, inst $ B <$> b)
    | (n, (_, b)) <- zip [0..] $ Vector.toList liftedBodies
    ]
  where
    inst = Lifted.bindOperand (unvar (Lifted.Global . inventName) pure)
    inventName (Tele tele) = x <> fromMaybe "" hint <> shower tele
      where Hint hint = fst $ liftedBodies Vector.! tele
