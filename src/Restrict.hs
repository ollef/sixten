{-# LANGUAGE FlexibleContexts, OverloadedStrings, RecursiveDo, ViewPatterns #-}
module Restrict where

import Control.Monad.Except
import qualified Bound.Scope.Simple as Simple
import Data.Bifunctor
import Data.Maybe
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import Syntax
import qualified Syntax.Lifted as Lifted
import qualified Syntax.Restricted as Restricted
import Meta
import TCM
import Util

type Meta = MetaVar Lifted.Expr

varDir :: Meta s -> (NameHint, Direction)
varDir m = (metaHint m, dir)
  where
    dir = case metaType m of
      Lifted.Lit 1 -> Direct
      _ -> Indirect

type BodyM s = Restricted.Body (Meta s)
type ExprM s = Lifted.Expr (Meta s)
type LBodyM s = Restricted.LBody (Meta s)
type LStmtM s = Restricted.LStmt (Meta s)
type SExprM s = Lifted.SExpr (Meta s)

sizeDir :: Lifted.Expr v -> Direction
sizeDir (Lifted.Lit 1) = Direct
sizeDir _ = Indirect

sExprDir :: Lifted.SExpr v -> Direction
sExprDir (Lifted.Sized sz _) = sizeDir sz

simpleTeleDirs :: SimpleTelescope Lifted.Expr v -> Vector Direction
simpleTeleDirs (SimpleTelescope xs) = sizeDir . Simple.unscope . snd <$> xs

simpleTeleDirectedNames :: SimpleTelescope Lifted.Expr v -> Vector (NameHint, Direction)
simpleTeleDirectedNames tele = Vector.zip (simpleTeleNames tele) (simpleTeleDirs tele)

restrictBody
  :: SExprM s
  -> TCM s (LBodyM s)
restrictBody expr = do
  trp "restrictBody" $ show <$> expr
  modifyIndent succ
  result <- case expr of
    Lifted.Sized _ (Lifted.Lams tele lamScope) -> mdo
      vs <- forMSimpleTele tele $ \h s ->
        forall_ h $ instantiateVar ((vs Vector.!) . unTele) $ vacuous s
      let lamExpr = instantiateVar ((vs Vector.!) . unTele) $ vacuous lamScope
      lamExpr' <- restrictSExpr lamExpr
      let lamScope' = Simple.abstract (teleAbstraction vs) lamExpr'
      return $ Restricted.lamLBody (sExprDir lamExpr) (simpleTeleDirectedNames tele) lamScope'
    _ -> Restricted.mapLifted (Restricted.ConstantBody . Restricted.Constant) <$> restrictSExpr expr
  modifyIndent pred
  trp "restrictBody res" $ show <$> result
  return result

restrictSExpr
  :: SExprM s
  -> TCM s (LStmtM s)
restrictSExpr (Lifted.Sized sz expr) = do
  rsz <- restrictExpr sz $ Restricted.pureLifted
                         $ Restricted.Sized (Restricted.Lit 1)
                         $ Restricted.Operand $ Restricted.Lit 1
  restrictExpr expr rsz

restrictSExprSize
  :: SExprM s
  -> TCM s (LStmtM s, LStmtM s)
restrictSExprSize (Lifted.Sized sz expr) = do
  rsz <- restrictConstantSize 1 sz
  rexpr <- restrictExpr expr rsz
  return (rexpr, rsz)

restrictConstantSize
  :: Literal
  -> ExprM s
  -> TCM s (LStmtM s)
restrictConstantSize sz expr =
  restrictExpr expr $ Restricted.pureLifted
                    $ Restricted.Sized (Restricted.Lit 1)
                    $ Restricted.Operand $ Restricted.Lit sz

restrictExpr
  :: ExprM s
  -> LStmtM s
  -> TCM s (LStmtM s)
restrictExpr expr sz = do
  trp "restrictExpr" $ show <$> expr
  modifyIndent succ
  result <- case expr of
    Lifted.Var v -> return $ Restricted.lSizedOperand sz $ Restricted.Local v
    Lifted.Global g -> return $ Restricted.lSizedOperand sz $ Restricted.Global g
    Lifted.Lit l -> return $ Restricted.lSizedOperand sz $ Restricted.Lit l
    Lifted.Con qc es -> Restricted.conLStmt sz qc <$> mapM restrictSExprSize es
    Lifted.Lams tele lamScope -> mdo
      vs <- forMSimpleTele tele $ \h s ->
        forall_ h $ instantiateVar ((vs Vector.!) . unTele) $ vacuous s
      let lamExpr = instantiateVar ((vs Vector.!) . unTele) $ vacuous lamScope
      lamExpr' <- restrictSExpr lamExpr
      let lamScope' = Simple.abstract (teleAbstraction vs) lamExpr'
      lamScope'' <- traverse (const $ throwError "liftBody") lamScope'
      return $ vacuous
             $ Restricted.liftLBody
             $ Restricted.lamLBody (sExprDir lamExpr) (simpleTeleDirectedNames tele) lamScope''
    Lifted.Call e es ->
      Restricted.callLStmt sz <$> restrictConstantSize 1 e <*> mapM restrictSExpr es
    Lifted.Let h e bodyScope -> do
      e' <- restrictSExpr e
      v <- forall_ h $ Lifted.sizeOf e
      let bodyExpr = instantiateVar (\() -> v) bodyScope
      bodyExpr' <- restrictExpr bodyExpr sz
      let bodyScope' = Simple.abstract1 v bodyExpr'
      return $ Restricted.letLStmt h e' bodyScope'
    Lifted.Case e brs -> Restricted.caseLStmt
                     <$> restrictSExpr e
                     <*> restrictBranches brs
    Lifted.Prim p -> Restricted.primLStmt sz <$> mapM (restrictConstantSize 1) p
  modifyIndent pred
  trp "restrictExpr res: " $ show <$> result
  return result
  where
    restrictBranches (SimpleConBranches cbrs) = Restricted.conLStmtBranches
      <$> mapM (restrictConBranch sz) cbrs
    restrictBranches (SimpleLitBranches lbrs def) = Restricted.litLStmtBranches
      <$> sequence [(,) l <$> restrictExpr e sz | (l, e) <- lbrs]
      <*> restrictExpr def sz

restrictConBranch
  :: LStmtM s
  -> ( QConstr
     , SimpleTelescope Lifted.Expr (Meta s)
     , Simple.Scope Tele Lifted.Expr (Meta s)
     )
  -> TCM s
     ( QConstr
     , Vector (NameHint, Simple.Scope Tele Restricted.LStmt (Meta s))
     , Simple.Scope Tele Restricted.LStmt (Meta s)
     )
restrictConBranch sz (qc, tele, brScope) = mdo
  tele' <- forMSimpleTele tele $ \h s -> do
    let e = instantiateVar ((vs Vector.!) . unTele) s
    v <- forall_ h e
    e' <- restrictConstantSize 1 e
    return (v, e')
  let vs = fst <$> tele'
      brExpr = instantiateVar ((vs Vector.!) . unTele) brScope
      abstr = teleAbstraction vs
      tele'' = bimap metaHint (Simple.abstract abstr) <$> tele'
  brExpr' <- restrictExpr brExpr sz
  let brScope' = Simple.abstract abstr brExpr'
  return (qc, tele'', brScope')

liftProgram :: Name -> [(Name, LBodyM s)] -> [(Name, BodyM s)]
liftProgram passName xs = xs >>= uncurry (liftBody passName)

liftBody :: Name -> Name -> LBodyM s -> [(Name, BodyM s)]
liftBody passName x (Restricted.Lifted liftedFunctions (Simple.Scope body))
  = (x, inst body)
  : [ (inventName n, inst $ B <$> b)
    | (n, (_, b)) <- zip [0..]
                   $ Vector.toList
                   $ second Restricted.FunctionBody <$> liftedFunctions
    ]
  where
    inst = Restricted.bindOperand (unvar (Restricted.Global . inventName) pure)
    inventName (Tele tele) = x <> fromMaybe "" hint <> passName <> shower tele
      where Hint hint = fst $ liftedFunctions Vector.! tele
