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
  :: AbstractM
  -> TCM AbstractM
whnf = whnf' False

whnf'
  :: Bool
  -> AbstractM
  -> TCM AbstractM
whnf' expandTypeReps expr = do
  modifyIndent succ
  res <- case expr of
    Var v -> refineVar v $ whnf' expandTypeReps
    Global g -> do
      (d, _) <- definition g
      case d of
        Definition e -> whnf' expandTypeReps e
        DataDefinition _ e | expandTypeReps -> whnf' expandTypeReps e
        _ -> return expr
    Con _ -> return expr
    Lit _ -> return expr
    Pi {} -> return expr
    Lam {} -> return expr
    Builtin.AddInt x y -> binOp 0 (+) Builtin.AddInt (whnf' expandTypeReps) x y
    Builtin.MaxInt x y -> binOp 0 max Builtin.MaxInt (whnf' expandTypeReps) x y
    App e1 p e2 -> do
      e1' <- whnf' expandTypeReps e1
      case e1' of
        Lam _ p' _ s | p == p' -> whnf' expandTypeReps $ Util.instantiate1 e2 s
        _ -> return expr
    Let _ e s -> whnf' expandTypeReps $ instantiate1 e s
    Case e brs -> do
      e' <- whnf' expandTypeReps e
      chooseBranch e' brs $ whnf' expandTypeReps
  modifyIndent pred
  return res

normalise
  :: AbstractM
  -> TCM AbstractM
normalise expr = do
  logMeta 40 "normalise e" expr
  modifyIndent succ
  res <- case expr of
    Var v -> refineVar v normalise
    Global g -> do
      (d, _) <- definition g
      case d of
        Definition e -> normalise e
        _ -> return expr
    Con _ -> return expr
    Lit _ -> return expr
    Pi n p a s -> normaliseScope n p (Pi n p) a s
    Lam n p a s -> normaliseScope n p (Lam n p) a s
    Builtin.AddInt x y -> binOp 0 (+) Builtin.AddInt normalise x y
    Builtin.MaxInt x y -> binOp 0 max Builtin.MaxInt normalise x y
    App e1 p e2 -> do
      e1' <- normalise e1
      e2' <- normalise e2
      case e1' of
        Lam _ p' _ s | p == p' -> normalise $ Util.instantiate1 e2' s
        _ -> return $ App e1' p e2'
    Let _ e s -> do
      e' <- normalise e
      normalise $ instantiate1 e' s
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
            <$> sequence [(,) l <$> normalise br | (l, br) <- lbrs]
            <*> normalise def
          NoBranches typ -> NoBranches
            <$> normalise typ
        _ -> return res
  modifyIndent pred
  logMeta 40 "normalise res" res
  return res
  where
    normaliseTelescope tele scope = do
      avs <- forTeleWithPrefixM tele $ \h a s avs -> do
        t' <- normalise $ instantiateTele pure (snd <$> avs) s
        v <- forall h t'
        return (a, v)

      let vs = snd <$> avs
          abstr = teleAbstraction vs
      e' <- normalise $ instantiateTele pure vs scope
      scope' <- abstractM abstr e'
      tele' <- forM avs $ \(a, v) -> do
        s <- abstractM abstr $ metaType v
        return (metaHint v, a, s)
      return (Telescope tele', scope')
    normaliseScope h _ c t s = do
      t' <- normalise t
      x <- forall h t'
      ns <- normalise $ Util.instantiate1 (pure x) s
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
  k $ instantiateTele snd (Vector.drop (Vector.length argsv - numConArgs) argsv) chosenBranch
  where
    argsv = Vector.fromList args
    (numConArgs, chosenBranch) = case [(teleLength tele, br) | (qc', tele, br) <- NonEmpty.toList cbrs, qc == qc'] of
      [br] -> br
      _ -> error "Normalise.chooseBranch"
chooseBranch e brs _ = return $ Case e brs
