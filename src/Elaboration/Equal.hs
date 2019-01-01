{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
module Elaboration.Equal where

import Protolude

import Control.Monad.Fail
import Control.Monad.Trans.Maybe
import qualified Data.List.NonEmpty as NonEmpty
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Elaboration.MetaVar
import Elaboration.Monad
import Elaboration.Normalise
import Syntax
import Syntax.Core
import TypedFreeVar
import Util

type Equal = MaybeT Elaborate
type MonadEqual m = (MonadElaborate m, Alternative m, MonadFail m)

exec
  :: Monad m
  => MaybeT m a
  -> m Bool
exec m = do
  res <- runMaybeT m
  case res of
    Nothing -> return False
    Just _ -> return True

expr :: MonadEqual m => CoreM -> CoreM -> m CoreM
expr type1 type2 = do
  type1' <- whnf type1
  type2' <- whnf type2
  expr' type1' type2'

expr' :: MonadEqual m => CoreM -> CoreM -> m CoreM
expr' (Var v1) (Var v2) = Var <$> eq v1 v2
expr' (Meta m1 es1) (Meta m2 es2) = Meta <$> eq m1 m2 <*> arguments es1 es2
expr' (Global g1) (Global g2) = Global <$> eq g1 g2
expr' (Con c1) (Con c2) = Con <$> eq c1 c2
expr' (Lit l1) (Lit l2) = Lit <$> eq l1 l2
expr' (Pi h1 p1 t1 s1) (Pi h2 p2 t2 s2) = abstraction pi_ h1 p1 t1 s1 h2 p2 t2 s2
expr' (Lam h1 p1 t1 s1) (Lam h2 p2 t2 s2) = abstraction lam h1 p1 t1 s1 h2 p2 t2 s2
expr' (App e1 p1 e1') (App e2 p2 e2')
  = App <$> expr e1 e2 <*> eq p1 p2 <*> expr e1' e2'
-- expr (Let ds1 s1) (Let ds2 s2) -- can't happen due to whnf
expr' (Case e1 brs1 t1) (Case e2 brs2 t2)
  = Case <$> expr e1 e2 <*> branches brs1 brs2 <*> expr t1 t2
expr' (ExternCode e1 t1) (ExternCode e2 t2)
  = ExternCode <$> extern e1 e2 <*> expr t1 t2
expr' (SourceLoc _ e1) e2 = expr' e1 e2
expr' e1 (SourceLoc _ e2) = expr' e1 e2
-- Eta-expand
expr' (Lam h p t s) e2 =
  extendContext h p t $ \v ->
    expr (instantiate1 (pure v) s) (App e2 p $ pure v)
expr' e1 (Lam h p t s) =
  extendContext h p t $ \v ->
    expr (App e1 p $ pure v) (instantiate1 (pure v) s)
-- Eta-reduce
expr' (etaReduce -> Just e1) e2 = expr e1 e2
expr' e1 (etaReduce -> Just e2) = expr e1 e2
expr' _ _ = fail "not equal"

arguments
  :: MonadEqual m
  => Vector (Plicitness, CoreM)
  -> Vector (Plicitness, CoreM)
  -> m (Vector (Plicitness, CoreM))
arguments es1 es2 = do
  guard $ Vector.length es1 == Vector.length es2
  let go (p1, e1) (p2, e2) = (,) <$> eq p1 p2 <*> expr e1 e2
  Vector.zipWithM go es1 es2

abstraction
  :: MonadEqual m
  => (FreeV -> CoreM -> b)
  -> NameHint -> Plicitness -> CoreM -> Scope1 (Expr MetaVar) FreeV
  -> NameHint -> Plicitness -> CoreM -> Scope1 (Expr MetaVar) FreeV
  -> m b
abstraction c h1 p1 t1 s1 h2 p2 t2 s2 = do
  let h = h1 <> h2
  p <- eq p1 p2
  t <- expr t1 t2
  extendContext h p t $ \v -> do
    s <- expr (instantiate1 (pure v) s1) (instantiate1 (pure v) s2)
    return $ c v s

branches
  :: MonadEqual m
  => Branches Plicitness (Expr MetaVar) FreeV
  -> Branches Plicitness (Expr MetaVar) FreeV
  -> m (Branches Plicitness (Expr MetaVar) FreeV)
branches (ConBranches cbrs1) (ConBranches cbrs2) = do
  guard $ length cbrs1 == length cbrs2
  ConBranches <$> zipWithM conBranch cbrs1 cbrs2
branches (LitBranches lbrs1 def1) (LitBranches lbrs2 def2) = do
  guard $ length lbrs1 == length lbrs2
  LitBranches <$> sequence (NonEmpty.zipWith litBranch lbrs1 lbrs2) <*> expr def1 def2
branches _ _ = fail "not equal"

conBranch
  :: MonadEqual m
  => ConBranch Plicitness (Expr MetaVar) FreeV
  -> ConBranch Plicitness (Expr MetaVar) FreeV
  -> m (ConBranch Plicitness (Expr MetaVar) FreeV)
conBranch (ConBranch c1 tele1 s1) (ConBranch c2 tele2 s2) = do
  c <- eq c1 c2
  guard $ teleLength tele1 == teleLength tele2
  teleExtendContext tele1 $ \vs -> do
    let
      types2 = forTele tele2 $ \_ _ s -> instantiateTele pure vs s
      go v type2 = do
        t <- expr (varType v) type2
        return $ v { varType = t }
    vs' <- Vector.zipWithM go vs types2
    let e1 = instantiateTele pure vs' s1
        e2 = instantiateTele pure vs' s2
    e <- expr e1 e2
    return $ conBranchTyped c vs' e

litBranch
  :: MonadEqual m
  => LitBranch (Expr MetaVar) FreeV
  -> LitBranch (Expr MetaVar) FreeV
  -> m (LitBranch (Expr MetaVar) FreeV)
litBranch (LitBranch l1 e1) (LitBranch l2 e2)
  = LitBranch <$> eq l1 l2 <*> expr e1 e2

extern
  :: MonadEqual m
  => Extern CoreM
  -> Extern CoreM
  -> m (Extern CoreM)
extern (Extern lang1 parts1) (Extern lang2 parts2) = do
  lang <- eq lang1 lang2
  guard $ length parts1 == length parts2
  let go (ExternPart t1) (ExternPart t2) = ExternPart <$> eq t1 t2
      go (ExprMacroPart e1) (ExprMacroPart e2) = ExprMacroPart <$> expr e1 e2
      go (TypeMacroPart t1) (TypeMacroPart t2) = TypeMacroPart <$> expr t1 t2
      go (TargetMacroPart m1) (TargetMacroPart m2) = TargetMacroPart <$> eq m1 m2
      go _ _ = fail "not equal"
  Extern lang <$> zipWithM go parts1 parts2

eq :: (Eq b, Alternative m, Monad m) => b -> b -> m b
eq x y = do
  guard $ x == y
  return x
