{-# LANGUAGE FlexibleContexts, OverloadedStrings, RecursiveDo #-}
module Restrict where

import Control.Monad.Except
import qualified Bound.Scope.Simple as Simple
import Data.Bifunctor
import Data.Bitraversable
import Data.Maybe
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import Syntax
import qualified Syntax.Converted as Converted
import qualified Syntax.Restricted as Restricted
import Meta
import TCM
import Util

type Meta = MetaVar Converted.Expr

varDir :: Meta s -> (NameHint, Direction)
varDir m = (metaHint m, dir)
  where
    dir = case metaType m of
      Converted.Lit 1 -> Direct
      _ -> Indirect

type BodyM s = Restricted.Body (Meta s)
type ExprM s = Converted.Expr (Meta s)
type LBodyM s = Restricted.LBody (Meta s)
type LStmtM s = Restricted.LStmt (Meta s)
type SExprM s = Converted.SExpr (Meta s)

teleDirectedNames :: Telescope Simple.Scope Direction Converted.Expr v -> Vector (NameHint, Direction)
teleDirectedNames tele = Vector.zip (teleNames tele) (teleAnnotations tele)

restrictBody
  :: SExprM s
  -> TCM s (LBodyM s)
restrictBody expr = do
  trp "restrictBody" $ show <$> expr
  modifyIndent succ
  result <- case expr of
    Converted.Sized _ (Converted.Lams retDir tele lamScope) -> mdo
      vs <- forMTele tele $ \h _dir s ->
        forall_ h $ instantiateVar ((vs Vector.!) . unTele) $ vacuous s
      let lamExpr = instantiateVar ((vs Vector.!) . unTele) $ vacuous lamScope
      lamExpr' <- restrictSExpr lamExpr
      let lamScope' = Simple.abstract (teleAbstraction vs) lamExpr'
      return $ Restricted.lamLBody retDir (teleDirectedNames tele) lamScope'
    _ -> Restricted.mapLifted (Restricted.ConstantBody . Restricted.Constant (Converted.sExprDir expr)) <$> restrictSExpr expr
  modifyIndent pred
  trp "restrictBody res" $ show <$> result
  return result

restrictSExpr
  :: SExprM s
  -> TCM s (LStmtM s)
restrictSExpr (Converted.Sized sz expr) = do
  rsz <- restrictConstantSize 1 sz
  restrictExpr expr rsz

restrictSExprSize
  :: SExprM s
  -> TCM s (LStmtM s, LStmtM s)
restrictSExprSize (Converted.Sized sz expr) = do
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
    Converted.Var v -> return $ Restricted.lSizedOperand sz $ Restricted.Local v
    Converted.Global g -> return $ Restricted.lSizedOperand sz $ Restricted.Global g
    Converted.Lit l -> return $ Restricted.lSizedOperand sz $ Restricted.Lit l
    Converted.Con qc es -> Restricted.conLStmt sz qc <$> mapM restrictSExprSize es
    Converted.Lams retDir tele lamScope -> mdo
      vs <- forMTele tele $ \h _dir s ->
        forall_ h $ instantiateVar ((vs Vector.!) . unTele) $ vacuous s
      let lamExpr = instantiateVar ((vs Vector.!) . unTele) $ vacuous lamScope
      lamExpr' <- restrictSExpr lamExpr
      let lamScope' = Simple.abstract (teleAbstraction vs) lamExpr'
      lamScope'' <- traverse (const $ throwError "liftBody") lamScope'
      return $ vacuous
             $ Restricted.liftLBody
             $ Restricted.lamLBody retDir (teleDirectedNames tele) lamScope''
    Converted.Call retDir e es ->
      Restricted.callLStmt retDir sz <$> restrictConstantSize 1 e <*> mapM (bitraverse restrictSExpr pure) es
    Converted.Let h e bodyScope -> do
      e' <- restrictSExpr e
      v <- forall_ h $ Converted.sizeOf e
      let bodyExpr = instantiateVar (\() -> v) bodyScope
      bodyExpr' <- restrictExpr bodyExpr sz
      let bodyScope' = Simple.abstract1 v bodyExpr'
      return $ Restricted.letLStmt h e' bodyScope'
    Converted.Case e brs -> Restricted.caseLStmt
                     <$> restrictSExpr e
                     <*> restrictBranches brs
    Converted.Prim p -> Restricted.primLStmt sz <$> mapM (restrictConstantSize 1) p
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
     , Telescope Simple.Scope () Converted.Expr (Meta s)
     , Simple.Scope Tele Converted.Expr (Meta s)
     )
  -> TCM s
     ( QConstr
     , Vector (NameHint, Simple.Scope Tele Restricted.LStmt (Meta s))
     , Simple.Scope Tele Restricted.LStmt (Meta s)
     )
restrictConBranch sz (qc, tele, brScope) = mdo
  trp "restrictConBranch" $ show <$> Simple.fromScope brScope
  modifyIndent succ
  vs <- forMTele tele $ \h () s ->
    forall_ h $ instantiateVar ((vs Vector.!) . unTele) s

  sizes <- forM vs $ restrictConstantSize 1 . metaType

  let brExpr = instantiateVar ((vs Vector.!) . unTele) brScope
      abstr = teleAbstraction vs
      tele' = Vector.zip (metaHint <$> vs) $ Simple.abstract abstr <$> sizes

  brExpr' <- restrictExpr brExpr sz
  let brScope' = Simple.abstract abstr brExpr'
  modifyIndent pred
  trp "restrictConBranch res" $ show <$> Simple.fromScope brScope'
  return (qc, tele', brScope')

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
