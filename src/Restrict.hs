{-# LANGUAGE FlexibleContexts, OverloadedStrings, ViewPatterns #-}
module Restrict where

import qualified Bound.Scope.Simple as Simple
import Data.Bifunctor
import Data.Hashable
import Data.Maybe
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Syntax
import qualified Syntax.Lambda as Lambda
import qualified Syntax.Lifted as Lifted
import Meta
import TCM
import Util

scopeDir :: Simple.Scope b Lambda.SExpr v -> Lifted.Direction
scopeDir (Simple.Scope (Lambda.Sized (Lambda.Lit 1) _)) = Lifted.Direct
scopeDir _ = Lifted.Indirect

simpleTeleDirs :: SimpleTelescope Lambda.Expr v -> Vector Lifted.Direction
simpleTeleDirs (SimpleTelescope xs) = go . snd <$> xs
  where
    go (Simple.Scope (Lambda.Lit 1)) = Lifted.Direct
    go _ = Lifted.Indirect

simpleTeleDirectedNames :: SimpleTelescope Lambda.Expr v -> Vector (NameHint, Lifted.Direction)
simpleTeleDirectedNames tele = Vector.zip (simpleTeleNames tele) (simpleTeleDirs tele)

restrictBody
  :: (Eq v, Hashable v, Show v)
  => Lambda.SExpr v
  -> TCM s (Lifted.LBody v)
restrictBody expr = case expr of
  (simpleBindingsViewM Lambda.lamView -> Just (tele, s)) ->
    Lifted.lamLBody (scopeDir s) (simpleTeleDirectedNames tele) <$> restrictSScope s
  _ -> Lifted.mapLifted Lifted.ConstantBody <$> restrictSExpr expr

restrictSExpr
  :: (Eq v, Hashable v, Show v)
  => Lambda.SExpr v
  -> TCM s (Lifted.LStmt v)
restrictSExpr (Lambda.Sized sz expr) = do
  rsz <- restrictExpr sz $ Lifted.pureLifted
                         $ Lifted.Sized (Lifted.Lit 1)
                         $ Lifted.Operand $ Lifted.Lit 1
  restrictExpr expr rsz

restrictSExprSize
  :: (Eq v, Hashable v, Show v)
  => Lambda.SExpr v
  -> TCM s (Lifted.LStmt v, Lifted.LStmt v)
restrictSExprSize (Lambda.Sized sz expr) = do
  rsz <- restrictConstantSize sz 1
  rexpr <- restrictExpr expr rsz
  return (rexpr, rsz)

restrictConstantSize
  :: (Eq v, Hashable v, Show v)
  => Lambda.Expr v
  -> Literal
  -> TCM s (Lifted.LStmt v)
restrictConstantSize expr sz =
  restrictExpr expr $ Lifted.pureLifted
                    $ Lifted.Sized (Lifted.Lit 1)
                    $ Lifted.Operand $ Lifted.Lit sz

restrictExpr
  :: (Eq v, Hashable v, Show v)
  => Lambda.Expr v
  -> Lifted.LStmt v
  -> TCM s (Lifted.LStmt v)
restrictExpr expr sz = do
  trp "restrictExpr" $ show <$> expr
  modifyIndent succ
  result <- case expr of
    Lambda.Var v -> return $ Lifted.lSizedOperand sz $ Lifted.Local v
    Lambda.Global g -> return $ Lifted.lSizedOperand sz $ Lifted.Global g
    Lambda.Lit l -> return $ Lifted.lSizedOperand sz $ Lifted.Lit l
    Lambda.Case e brs -> Lifted.caseLStmt <$> restrictSExprSize e <*> restrictBranches brs
    Lambda.Con qc es -> Lifted.conLStmt sz qc <$> mapM restrictSExprSize es
    (simpleBindingsViewM Lambda.lamView . Lambda.Sized (Lambda.Global "restrictExpr-impossible") -> Just (tele, s)) ->
      fmap Lifted.liftLBody $ Lifted.lamLBody (scopeDir s) (simpleTeleDirectedNames tele) <$> restrictSScope s
    (Lambda.appsView -> (e, es)) ->
      Lifted.callLStmt sz <$> restrictConstantSize e 1 <*> mapM restrictSExpr es
  modifyIndent pred
  trp "restrictExpr res: " $ show <$> result
  return result
  where
    restrictBranches (SimpleConBranches cbrs) = Lifted.conLStmtBranches
      <$> sequence [(,,) c <$> restrictTele tele <*> restrictScope s sz | (c, tele, s) <- cbrs]
    restrictBranches (SimpleLitBranches lbrs def) = Lifted.litLStmtBranches
      <$> sequence [(,) l <$> restrictExpr e sz | (l, e) <- lbrs]
      <*> restrictExpr def sz
    restrictTele = mapM (\(h, s) -> (,) h <$> restrictConstantSizeScope s 1)
                 . unSimpleTelescope

restrictScope
  :: (Eq b, Eq v, Show b, Show v, Hashable b, Hashable v)
  => Simple.Scope b Lambda.Expr v
  -> Lifted.LStmt v
  -> TCM s (Simple.Scope b Lifted.LStmt v)
restrictScope expr sz
  = Simple.toScope <$> restrictExpr (Simple.fromScope expr) (F <$> sz)

restrictSScope
  :: (Eq b, Eq v, Show b, Show v, Hashable b, Hashable v)
  => Simple.Scope b Lambda.SExpr v
  -> TCM s (Simple.Scope b Lifted.LStmt v)
restrictSScope s = Simple.toScope <$> restrictSExpr (Simple.fromScope s)

restrictConstantSizeScope
  :: (Eq b, Eq v, Show b, Show v, Hashable b, Hashable v)
  => Simple.Scope b Lambda.Expr v
  -> Literal
  -> TCM s (Simple.Scope b Lifted.LStmt v)
restrictConstantSizeScope expr sz
  = Simple.toScope <$> restrictConstantSize (Simple.fromScope expr) sz

liftProgram :: [(Name, Lifted.LBody v)] -> [(Name, Lifted.Body v)]
liftProgram xs = xs >>= uncurry liftBody

liftBody :: Name -> Lifted.LBody v -> [(Name, Lifted.Body v)]
liftBody x (Lifted.Lifted liftedFunctions (Simple.Scope body))
  = (x, inst body)
  : [ (inventName n, inst $ B <$> b)
    | (n, (_, b)) <- zip [0..]
                   $ Vector.toList
                   $ second Lifted.FunctionBody <$> liftedFunctions
    ]
  where
    inst = Lifted.bindOperand (unvar (Lifted.Global . inventName) pure)
    inventName (Tele tele) = x <> fromMaybe "" hint <> shower tele
      where Hint hint = fst $ liftedFunctions Vector.! tele
