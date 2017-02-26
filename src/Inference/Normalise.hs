{-# LANGUAGE FlexibleContexts, MonadComprehensions, ViewPatterns #-}
module Inference.Normalise where

import Control.Monad.Except
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Vector as Vector

import qualified Builtin
import Meta
import TCM
import Syntax
import Syntax.Abstract
import Util

whnf
  :: MetaVary Expr v
  => Expr v
  -> TCM (Expr v)
whnf expr = do
  modifyIndent succ
  res <- case expr of
    Var v -> refineVar v whnf
    Global g -> do
      (d, _) <- definition g
      case d of
        Definition e -> whnf e
        _ -> return expr
    Con _ -> return expr
    Lit _ -> return expr
    Pi {} -> return expr
    Lam {} -> return expr
    Builtin.AddInt x y -> binOp 0 (+) Builtin.AddInt whnf x y
    Builtin.MaxInt x y -> binOp 0 max Builtin.MaxInt whnf x y
    App e1 p e2 -> do
      e1' <- whnf e1
      case e1' of
        Lam _ p' _ s | p == p' -> do
          e2' <- whnf e2
          whnf $ Util.instantiate1 e2' s
        _ -> return expr
    Let _ e s -> whnf $ instantiate1 e s
    Case e brs -> do
      e' <- whnf e
      chooseBranch e' brs whnf
  modifyIndent pred
  return res

normaliseM
  :: Expr MetaA
  -> TCM (Expr MetaA)
normaliseM expr = do
  logMeta 40 "normaliseM e" expr
  modifyIndent succ
  res <- case expr of
    Var v -> refineVar v normaliseM
    Global g -> do
      (d, _) <- definition g
      case d of
        Definition e -> normaliseM e
        _ -> return expr
    Con _ -> return expr
    Lit _ -> return expr
    Pi n p a s -> normaliseScope n p (Pi n p) a s
    Lam n p a s -> normaliseScope n p (Lam n p) a s
    Builtin.AddInt x y -> binOp 0 (+) Builtin.AddInt normaliseM x y
    Builtin.MaxInt x y -> binOp 0 max Builtin.MaxInt normaliseM x y
    App e1 p e2 -> do
      e1' <- normaliseM e1
      e2' <- normaliseM e2
      case e1' of
        Lam _ p' _ s | p == p' -> normaliseM $ Util.instantiate1 e2' s
        _ -> return $ App e1' p e2'
    Let _ e s -> do
      e' <- normaliseM e
      normaliseM $ instantiate1 e' s
    Case e brs -> do
      e' <- whnf e
      res <- chooseBranch e' brs whnf
      case res of
        Case e'' brs' -> Case e'' <$> case brs' of
          ConBranches cbrs -> ConBranches
            <$> sequence
              [ uncurry ((,,) qc) <$> normaliseTelescope tele s
              | (qc, tele, s) <- cbrs
              ]
          LitBranches lbrs def -> LitBranches
            <$> sequence [(,) l <$> normaliseM br | (l, br) <- lbrs]
            <*> normaliseM def
          NoBranches typ -> NoBranches
            <$> normaliseM typ
        _ -> return res
  modifyIndent pred
  logMeta 40 "normaliseM res" res
  return res
  where
    normaliseTelescope tele scope = do
      avs <- forTeleWithPrefixM tele $ \h a s avs -> do
        t' <- normaliseM $ instantiateTele pure (snd <$> avs) s
        v <- forall h a t'
        return (a, v)

      let vs = snd <$> avs
          abstr = teleAbstraction vs
      e' <- normaliseM $ instantiateTele pure vs scope
      scope' <- abstractM abstr e'
      tele' <- forM avs $ \(a, v) -> do
        s <- abstractM abstr $ metaType v
        return (metaHint v, a, s)
      return (Telescope tele', scope')
    normaliseScope h p c t s = do
      t' <- normaliseM t
      x <- forall h p t'
      ns <- normaliseM $ Util.instantiate1 (pure x) s
      c t' <$> abstract1M x ns

binOp
  :: Monad m
  => Literal
  -> (Literal -> Literal -> Literal)
  -> (Expr v -> Expr v -> Expr v)
  -> (Expr v -> m (Expr v))
  -> Expr v
  -> Expr v
  -> m (Expr v)
binOp zero op cop norm x y = do
    x' <- norm x
    y' <- norm y
    case (x', y') of
      (Lit m, _) | m == zero -> return y'
      (_, Lit n) | n == zero -> return x'
      (Lit m, Lit n) -> return $ Lit $ op m n
      _ -> return $ cop x' y'

chooseBranch
  :: Monad m
  => Expr v
  -> Branches QConstr Plicitness Expr v
  -> (Expr v -> m (Expr v))
  -> m (Expr v)
chooseBranch (Lit l) (LitBranches lbrs def) k = k chosenBranch
  where
    chosenBranch = head $ [br | (l', br) <- NonEmpty.toList lbrs, l == l'] ++ [def]
chooseBranch (appsView -> (Con qc, args)) (ConBranches cbrs) k =
  k $ instantiateTele snd (Vector.fromList args) chosenBranch
  where
    chosenBranch = case [br | (qc', _, br) <- NonEmpty.toList cbrs, qc == qc'] of
      [br] -> br
      _ -> error "Normalise.chooseBranch"
chooseBranch e brs _ = return $ Case e brs
