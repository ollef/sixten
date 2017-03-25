{-# LANGUAGE FlexibleContexts, MonadComprehensions, ViewPatterns #-}
module Inference.Normalise where

import Control.Monad.Except
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Vector as Vector

import qualified Builtin
import Meta
import VIX
import Syntax
import Syntax.Abstract
import Util

whnf
  :: AbstractM
  -> VIX AbstractM
whnf = whnf' False

whnf'
  :: Bool
  -> AbstractM
  -> VIX AbstractM
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
    Builtin.SubInt x y -> binOp Nothing (Just 0) (-) Builtin.SubInt (whnf' expandTypeReps) x y
    Builtin.AddInt x y -> binOp (Just 0) (Just 0) (+) Builtin.AddInt (whnf' expandTypeReps) x y
    Builtin.MaxInt x y -> binOp (Just 0) (Just 0) max Builtin.MaxInt (whnf' expandTypeReps) x y
    App e1 p e2 -> do
      e1' <- whnf' expandTypeReps e1
      case e1' of
        Lam _ p' _ s | p == p' -> whnf' expandTypeReps $ Util.instantiate1 e2 s
        _ -> return expr
    Let _ e s -> whnf' expandTypeReps $ instantiate1 e s
    Case e brs retType -> do
      e' <- whnf' expandTypeReps e
      chooseBranch e' brs retType $ whnf' expandTypeReps
  modifyIndent pred
  return res

normalise
  :: AbstractM
  -> VIX AbstractM
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
    Builtin.SubInt x y -> binOp Nothing (Just 0) (-) Builtin.SubInt normalise x y
    Builtin.AddInt x y -> binOp (Just 0) (Just 0) (+) Builtin.AddInt normalise x y
    Builtin.MaxInt x y -> binOp (Just 0) (Just 0) max Builtin.MaxInt normalise x y
    App e1 p e2 -> do
      e1' <- normalise e1
      e2' <- normalise e2
      case e1' of
        Lam _ p' _ s | p == p' -> normalise $ Util.instantiate1 e2' s
        _ -> return $ App e1' p e2'
    Let _ e s -> do
      e' <- normalise e
      normalise $ instantiate1 e' s
    Case e brs retType -> do
      e' <- whnf e
      res <- chooseBranch e' brs retType whnf
      case res of
        Case e'' brs' retType' -> Case e'' <$> (case brs' of
          ConBranches cbrs -> ConBranches
            <$> sequence
              [ uncurry ((,,) qc) <$> normaliseTelescope tele s
              | (qc, tele, s) <- cbrs
              ]
          LitBranches lbrs def -> LitBranches
            <$> sequence [(,) l <$> normalise br | (l, br) <- lbrs]
            <*> normalise def)
          <*> normalise retType'
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
  => Maybe Literal
  -> Maybe Literal
  -> (Literal -> Literal -> Literal)
  -> (Expr v -> Expr v -> Expr v)
  -> (Expr v -> m (Expr v))
  -> Expr v
  -> Expr v
  -> m (Expr v)
binOp lzero rzero op cop norm x y = do
    x' <- norm x
    y' <- norm y
    case (x', y') of
      (Lit m, _) | Just m == lzero -> return y'
      (_, Lit n) | Just n == rzero -> return x'
      (Lit m, Lit n) -> return $ Lit $ op m n
      _ -> return $ cop x' y'

chooseBranch
  :: Monad m
  => Expr v
  -> Branches QConstr Plicitness Expr v
  -> Expr v
  -> (Expr v -> m (Expr v))
  -> m (Expr v)
chooseBranch (Lit l) (LitBranches lbrs def) _ k = k chosenBranch
  where
    chosenBranch = head $ [br | (l', br) <- NonEmpty.toList lbrs, l == l'] ++ [def]
chooseBranch (appsView -> (Con qc, args)) (ConBranches cbrs) _ k =
  k $ instantiateTele snd (Vector.drop (Vector.length argsv - numConArgs) argsv) chosenBranch
  where
    argsv = Vector.fromList args
    (numConArgs, chosenBranch) = case [(teleLength tele, br) | (qc', tele, br) <- cbrs, qc == qc'] of
      [br] -> br
      _ -> error "Normalise.chooseBranch"
chooseBranch e brs retType _ = return $ Case e brs retType
