{-# LANGUAGE FlexibleContexts, MonadComprehensions, ViewPatterns #-}
module Inference.Normalise where

import Control.Monad.Except
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Meta
import Syntax
import Syntax.Abstract
import TypeRep(TypeRep)
import qualified TypeRep
import Util
import VIX

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
        Lam h p' t s | p == p' -> do
          eVar <- let_ h e t
          go (Util.instantiate1 (pure eVar) s) es'
        _ -> case apps f' es of
          Builtin.ProductTypeRep x y -> typeRepBinOp
            (Just TypeRep.Unit) (Just TypeRep.Unit)
            TypeRep.product Builtin.ProductTypeRep
            (whnf' expandTypeReps) x y
          Builtin.SumTypeRep x y -> typeRepBinOp
            (Just TypeRep.Unit) (Just TypeRep.Unit)
            TypeRep.sum Builtin.SumTypeRep
            (whnf' expandTypeReps) x y
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
  Global g -> do
    (d, _) <- definition g
    case d of
      Definition Concrete e -> whnf' expandTypeReps e
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
    Global g -> do
      (d, _) <- definition g
      case d of
        Definition Concrete e -> normalise e
        _ -> return expr
    Con _ -> return expr
    Lit _ -> return expr
    Pi n p a s -> normaliseScope n p (Pi n p) a s
    Lam n p a s -> normaliseScope n p (Lam n p) a s
    Builtin.ProductTypeRep x y -> typeRepBinOp
      (Just TypeRep.Unit) (Just TypeRep.Unit)
      TypeRep.product Builtin.ProductTypeRep
      normalise x y
    Builtin.SumTypeRep x y -> typeRepBinOp
      (Just TypeRep.Unit) (Just TypeRep.Unit)
      TypeRep.sum Builtin.SumTypeRep
      normalise x y
    Builtin.SubInt x y -> binOp Nothing (Just 0) (-) Builtin.SubInt normalise x y
    Builtin.AddInt x y -> binOp (Just 0) (Just 0) (+) Builtin.AddInt normalise x y
    Builtin.MaxInt x y -> binOp (Just 0) (Just 0) max Builtin.MaxInt normalise x y
    App e1 p e2 -> do
      e1' <- normalise e1
      case e1' of
        Lam h p' t s | p == p' -> do
          e2Var <- let_ h e2 t
          normalise $ Util.instantiate1 (pure e2Var) s
        _ -> do
          e2' <- normalise e2
          return $ App e1' p e2'
    Let _ e s -> do
      e' <- normalise e
      normalise $ instantiate1 e' s
    Case e brs retType -> do
      e' <- whnf e
      res <- chooseBranch e' brs retType normalise
      case res of
        Case e'' brs' retType' -> Case e'' <$> (case brs' of
          ConBranches cbrs -> ConBranches
            <$> sequence
              [ uncurry (ConBranch qc) <$> normaliseTelescope tele s
              | ConBranch qc tele s <- cbrs
              ]
          LitBranches lbrs def -> LitBranches
            <$> sequence [LitBranch l <$> normalise br | LitBranch l br <- lbrs]
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
        return $ TeleArg (metaHint v) a s
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

typeRepBinOp
  :: Monad m
  => Maybe TypeRep
  -> Maybe TypeRep
  -> (TypeRep -> TypeRep -> TypeRep)
  -> (Expr v -> Expr v -> Expr v)
  -> (Expr v -> m (Expr v))
  -> Expr v
  -> Expr v
  -> m (Expr v)
typeRepBinOp lzero rzero op cop norm x y = do
    x' <- norm x
    y' <- norm y
    case (x', y') of
      (Lit (TypeRep m), _) | Just m == lzero -> return y'
      (_, Lit (TypeRep n)) | Just n == rzero -> return x'
      (Lit (TypeRep m), Lit (TypeRep n)) -> return $ Lit $ TypeRep $ op m n
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
    chosenBranch = head $ [br | LitBranch l' br <- NonEmpty.toList lbrs, l == l'] ++ [def]
chooseBranch (appsView -> (Con qc, args)) (ConBranches cbrs) _ k =
  k $ instantiateTele snd (Vector.drop (Vector.length argsv - numConArgs) argsv) chosenBranch
  where
    argsv = Vector.fromList args
    (numConArgs, chosenBranch) = case [(teleLength tele, br) | ConBranch qc' tele br <- cbrs, qc == qc'] of
      [br] -> br
      _ -> error "Normalise.chooseBranch"
chooseBranch e brs retType _ = return $ Case e brs retType
