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
  logMeta 40 ("whnf e " ++ show expandTypeReps) expr
  res <- uncurry go $ appsView expr
  logMeta 40 ("whnf res " ++ show expandTypeReps) res
  modifyIndent pred
  return res
  where
    go f [] = whnfInner expandTypeReps f
    go f es@((p, e):es') = do
      f' <- whnfInner expandTypeReps f
      case f' of
        Lam _ p' _ s | p == p' -> go (Util.instantiate1 e s) es'
        _ -> case apps f' es of
          Builtin.SubInt x y -> binOp Nothing (Just 0) (-) Builtin.SubInt (whnf' expandTypeReps) x y
          Builtin.AddInt x y -> binOp (Just 0) (Just 0) (+) Builtin.AddInt (whnf' expandTypeReps) x y
          Builtin.MaxInt x y -> binOp (Just 0) (Just 0) max Builtin.MaxInt (whnf' expandTypeReps) x y
          expr' -> return expr'

whnfInner
  :: Bool
  -> AbstractM
  -> VIX AbstractM
whnfInner expandTypeReps expr = case expr of
  Var v -> refineVar v $ whnf' expandTypeReps
  Global g
    | isAbstract g -> return expr
    | otherwise -> do
      (d, _) <- definition g
      case d of
        Definition e -> whnf' expandTypeReps e
        DataDefinition _ e | expandTypeReps -> whnf' expandTypeReps e
        _ -> return expr
  Con _ -> return expr
  Lit _ -> return expr
  Pi {} -> return expr
  Lam {} -> return expr
  App {} -> return expr
  Let _ e s -> whnf' expandTypeReps $ instantiate1 e s
  Case e brs retType -> do
    e' <- whnf' expandTypeReps e
    retType' <- whnf' expandTypeReps retType
    chooseBranch e' brs retType' $ whnf' expandTypeReps
  ExternCode c retType -> ExternCode
    <$> mapM (whnf' expandTypeReps) c
    <*> whnf' expandTypeReps retType

normalise
  :: AbstractM
  -> VIX AbstractM
normalise expr = do
  logMeta 40 "normalise e" expr
  modifyIndent succ
  res <- case expr of
    Var v -> refineVar v normalise
    Global g
      | isAbstract g -> return expr
      | otherwise -> do
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
    ExternCode c retType -> ExternCode <$> mapM normalise c <*> normalise retType
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
  => Maybe Integer
  -> Maybe Integer
  -> (Integer -> Integer -> Integer)
  -> (Expr v -> Expr v -> Expr v)
  -> (Expr v -> m (Expr v))
  -> Expr v
  -> Expr v
  -> m (Expr v)
binOp lzero rzero op cop norm x y = do
    x' <- norm x
    y' <- norm y
    case (x', y') of
      (Lit (Integer m), _) | Just m == lzero -> return y'
      (_, Lit (Integer n)) | Just n == rzero -> return x'
      (Lit (Integer m), Lit (Integer n)) -> return $ Lit $ Integer $ op m n
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

-- TODO: Find a less hacky way to do this
isAbstract :: QName -> Bool
isAbstract Builtin.AddIntName = True
isAbstract Builtin.SubIntName = True
isAbstract Builtin.MaxIntName = True
isAbstract Builtin.FailName = True
isAbstract _ = False
