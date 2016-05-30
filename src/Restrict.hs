{-# LANGUAGE FlexibleContexts, OverloadedStrings, RecursiveDo, ViewPatterns #-}
module Restrict where

import qualified Bound.Scope.Simple as Simple
import Data.Bifunctor
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

type Meta = MetaVar Lambda.Expr

varDir :: Meta s -> (NameHint, Lifted.Direction)
varDir m = (metaHint m, dir)
  where
    dir = case metaType m of
      Lambda.Lit 1 -> Lifted.Direct
      _ -> Lifted.Indirect

type BodyM s = Lifted.Body (Meta s)
type ExprM s = Lambda.Expr (Meta s)
type LBodyM s = Lifted.LBody (Meta s)
type LStmtM s = Lifted.LStmt (Meta s)
type SExprM s = Lambda.SExpr (Meta s)

sizeDir :: Lambda.Expr v -> Lifted.Direction
sizeDir (Lambda.Lit 1) = Lifted.Direct
sizeDir _ = Lifted.Indirect

sExprDir :: Lambda.SExpr v -> Lifted.Direction
sExprDir (Lambda.Sized sz _) = sizeDir sz

simpleTeleDirs :: SimpleTelescope Lambda.Expr v -> Vector Lifted.Direction
simpleTeleDirs (SimpleTelescope xs) = sizeDir . Simple.unscope . snd <$> xs

simpleTeleDirectedNames :: SimpleTelescope Lambda.Expr v -> Vector (NameHint, Lifted.Direction)
simpleTeleDirectedNames tele = Vector.zip (simpleTeleNames tele) (simpleTeleDirs tele)

restrictBody
  :: SExprM s
  -> TCM s (LBodyM s)
restrictBody expr = case expr of
  (simpleBindingsViewM Lambda.lamView -> Just (tele, lamScope)) -> mdo
    vs <- forMSimpleTele tele $ \h s ->
      forall_ h $ instantiateVar ((vs Vector.!) . unTele) s
    let lamExpr = instantiateVar ((vs Vector.!) . unTele) lamScope
    lamExpr' <- restrictSExpr lamExpr
    let lamScope' = Simple.abstract (teleAbstraction vs) lamExpr'
    return $ Lifted.lamLBody (sExprDir lamExpr) (simpleTeleDirectedNames tele) lamScope'
  _ -> Lifted.mapLifted Lifted.ConstantBody <$> restrictSExpr expr

restrictSExpr
  :: SExprM s
  -> TCM s (LStmtM s)
restrictSExpr (Lambda.Sized sz expr) = do
  rsz <- restrictExpr sz $ Lifted.pureLifted
                         $ Lifted.Sized (Lifted.Lit 1)
                         $ Lifted.Operand $ Lifted.Lit 1
  restrictExpr expr rsz

restrictSExprSize
  :: SExprM s
  -> TCM s (LStmtM s, LStmtM s)
restrictSExprSize (Lambda.Sized sz expr) = do
  rsz <- restrictConstantSize sz 1
  rexpr <- restrictExpr expr rsz
  return (rexpr, rsz)

restrictConstantSize
  :: ExprM s
  -> Literal
  -> TCM s (LStmtM s)
restrictConstantSize expr sz =
  restrictExpr expr $ Lifted.pureLifted
                    $ Lifted.Sized (Lifted.Lit 1)
                    $ Lifted.Operand $ Lifted.Lit sz

restrictExpr
  :: ExprM s
  -> LStmtM s
  -> TCM s (LStmtM s)
restrictExpr expr sz = do
  trp "restrictExpr" $ show <$> expr
  modifyIndent succ
  result <- case expr of
    Lambda.Var v -> return $ Lifted.lSizedOperand sz $ Lifted.Local v
    Lambda.Global g -> return $ Lifted.lSizedOperand sz $ Lifted.Global g
    Lambda.Lit l -> return $ Lifted.lSizedOperand sz $ Lifted.Lit l
    Lambda.Case e brs -> Lifted.caseLStmt <$> restrictSExprSize e <*> restrictBranches brs
    Lambda.Con qc es -> Lifted.conLStmt sz qc <$> mapM restrictSExprSize es
    (simpleBindingsViewM Lambda.lamView . Lambda.Sized (Lambda.Global "restrictExpr-impossible") -> Just (tele, lamScope)) -> mdo
      vs <- forMSimpleTele tele $ \h s ->
        forall_ h $ instantiateVar ((vs Vector.!) . unTele) s
      let lamExpr = instantiateVar ((vs Vector.!) . unTele) lamScope
      lamExpr' <- restrictSExpr lamExpr
      let lamScope' = Simple.abstract (teleAbstraction vs) lamExpr'
      return $ Lifted.liftLBody varDir
             $ Lifted.lamLBody (sExprDir lamExpr) (simpleTeleDirectedNames tele) lamScope'
    (Lambda.appsView -> (e, es)) ->
      Lifted.callLStmt sz <$> restrictConstantSize e 1 <*> mapM restrictSExpr es
  modifyIndent pred
  trp "restrictExpr res: " $ show <$> result
  return result
  where
    restrictBranches (SimpleConBranches cbrs) = Lifted.conLStmtBranches
      <$> mapM (restrictConBranch sz) cbrs
    restrictBranches (SimpleLitBranches lbrs def) = Lifted.litLStmtBranches
      <$> sequence [(,) l <$> restrictExpr e sz | (l, e) <- lbrs]
      <*> restrictExpr def sz

restrictConBranch
  :: LStmtM s
  -> ( QConstr
     , SimpleTelescope Lambda.Expr (Meta s)
     , Simple.Scope Tele Lambda.Expr (Meta s)
     )
  -> TCM s
     ( QConstr
     , Vector (NameHint, Simple.Scope Tele Lifted.LStmt (Meta s))
     , Simple.Scope Tele Lifted.LStmt (Meta s)
     )
restrictConBranch sz (qc, tele, brScope) = mdo
  tele' <- forMSimpleTele tele $ \h s -> do
    let e = instantiateVar ((vs Vector.!) . unTele) s
    v <- forall_ h e
    e' <- restrictConstantSize e 1
    return (v, e')
  let vs = fst <$> tele'
      brExpr = instantiateVar ((vs Vector.!) . unTele) brScope
      abstr = teleAbstraction vs
      tele'' = bimap metaHint (Simple.abstract abstr) <$> tele'
  brExpr' <- restrictExpr brExpr sz
  let brScope' = Simple.abstract abstr brExpr'
  return (qc, tele'', brScope')

liftProgram :: [(Name, LBodyM s)] -> [(Name, BodyM s)]
liftProgram xs = xs >>= uncurry liftBody

liftBody :: Name -> LBodyM s -> [(Name, BodyM s)]
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
