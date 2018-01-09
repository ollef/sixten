{-# LANGUAGE FlexibleContexts, MonadComprehensions, ViewPatterns, RecursiveDo #-}
module Inference.Normalise where

import Control.Monad.Except
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Inference.Meta
import Syntax
import Syntax.Abstract
import TypeRep(TypeRep)
import qualified TypeRep
import Util
import VIX

-------------------------------------------------------------------------------
-- * Weak head normal forms
whnf
  :: (MonadIO m, MonadVIX m, MonadError Error m, MonadFix m)
  => AbstractM
  -> m AbstractM
whnf = whnf' WhnfArgs
  { expandTypeReps = False
  , handleUnsolvedConstraint = const $ return Nothing
  }

whnfExpandingTypeReps
  :: (MonadIO m, MonadVIX m, MonadError Error m, MonadFix m)
  => AbstractM
  -> m AbstractM
whnfExpandingTypeReps = whnf' WhnfArgs
  { expandTypeReps = True
  , handleUnsolvedConstraint = const $ return Nothing
  }

data WhnfArgs m = WhnfArgs
  { expandTypeReps :: !Bool
    -- ^ Should types be reduced to type representations (i.e. forget what the
    -- type is and only remember its representation)?
  , handleUnsolvedConstraint :: !(AbstractM -> m (Maybe AbstractM))
    -- ^ Allows whnf to try to solve an unsolved class constraint when they're
    -- encountered.
  }

whnf'
  :: (MonadIO m, MonadVIX m, MonadError Error m, MonadFix m)
  => WhnfArgs m
  -> AbstractM
  -> m AbstractM
whnf' args expr = do
  modifyIndent succ
  logMeta 40 "whnf e" expr
  res <- uncurry go $ appsView expr
  logMeta 40 "whnf res" res
  modifyIndent pred
  return res
  where
    go f [] = whnfInner args f
    go f es@((p, e):es') = do
      f' <- whnfInner args f
      case f' of
        Lam h p' t s | p == p' -> do
          eVar <- shared h p e t
          go (Util.instantiate1 (pure eVar) s) es'
        _ -> case apps f' es of
          Builtin.ProductTypeRep x y -> typeRepBinOp
            (Just TypeRep.UnitRep) (Just TypeRep.UnitRep)
            TypeRep.product Builtin.ProductTypeRep
            (whnf' args) x y
          Builtin.SumTypeRep x y -> typeRepBinOp
            (Just TypeRep.UnitRep) (Just TypeRep.UnitRep)
            TypeRep.sum Builtin.SumTypeRep
            (whnf' args) x y
          Builtin.SubInt x y -> binOp Nothing (Just 0) (-) Builtin.SubInt (whnf' args) x y
          Builtin.AddInt x y -> binOp (Just 0) (Just 0) (+) Builtin.AddInt (whnf' args) x y
          Builtin.MaxInt x y -> binOp (Just 0) (Just 0) max Builtin.MaxInt (whnf' args) x y
          expr'@(Builtin.UnsolvedConstraint typ) -> do
            msolution <- handleUnsolvedConstraint args typ
            case msolution of
              Nothing -> return expr'
              Just sol -> whnf' args sol
          expr' -> return expr'

whnfInner
  :: (MonadIO m, MonadVIX m, MonadError Error m, MonadFix m)
  => WhnfArgs m
  -> AbstractM
  -> m AbstractM
whnfInner args expr = case expr of
  Var v -> refineVar v $ whnf' args
  Global g -> do
    (d, _) <- definition g
    case d of
      Definition Concrete _ e -> whnf' args e
      DataDefinition _ e | expandTypeReps args -> whnf' args e
      _ -> return expr
  Con _ -> return expr
  Lit _ -> return expr
  Pi {} -> return expr
  (etaReduce -> Just expr') -> whnf' args expr'
  Lam {} -> return expr
  App {} -> return expr
  Let ds scope -> do
    e <- instantiateLetM ds scope
    whnf' args e
  Case e brs retType -> do
    e' <- whnf' args e
    retType' <- whnf' args retType
    chooseBranch e' brs retType' $ whnf' args
  ExternCode c retType -> ExternCode
    <$> mapM (whnf' args) c
    <*> whnf' args retType

normalise
  :: (MonadIO m, MonadVIX m, MonadError Error m, MonadFix m)
  => AbstractM
  -> m AbstractM
normalise expr = do
  logMeta 40 "normalise e" expr
  modifyIndent succ
  res <- case expr of
    Var v -> refineVar v normalise
    Global g -> do
      (d, _) <- definition g
      case d of
        Definition Concrete _ e -> normalise e
        _ -> return expr
    Con _ -> return expr
    Lit _ -> return expr
    Pi n p a s -> normaliseScope n p (Pi n p) a s
    (etaReduce -> Just expr') -> normalise expr'
    Lam n p a s -> normaliseScope n p (Lam n p) a s
    Builtin.ProductTypeRep x y -> typeRepBinOp
      (Just TypeRep.UnitRep) (Just TypeRep.UnitRep)
      TypeRep.product Builtin.ProductTypeRep
      normalise x y
    Builtin.SumTypeRep x y -> typeRepBinOp
      (Just TypeRep.UnitRep) (Just TypeRep.UnitRep)
      TypeRep.sum Builtin.SumTypeRep
      normalise x y
    Builtin.SubInt x y -> binOp Nothing (Just 0) (-) Builtin.SubInt normalise x y
    Builtin.AddInt x y -> binOp (Just 0) (Just 0) (+) Builtin.AddInt normalise x y
    Builtin.MaxInt x y -> binOp (Just 0) (Just 0) max Builtin.MaxInt normalise x y
    App e1 p e2 -> do
      e1' <- normalise e1
      case e1' of
        Lam h p' t s | p == p' -> do
          e2Var <- shared h p e2 t
          normalise $ Util.instantiate1 (pure e2Var) s
        _ -> do
          e2' <- normalise e2
          return $ App e1' p e2'
    Let ds scope -> do
      e <- instantiateLetM ds scope
      normalise e
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
      pvs <- forTeleWithPrefixM tele $ \h p s avs -> do
        t' <- normalise $ instantiateTele pure (snd <$> avs) s
        v <- forall h p t'
        return (p, v)

      let vs = snd <$> pvs
          abstr = teleAbstraction vs
      e' <- normalise $ instantiateTele pure vs scope
      scope' <- abstractM abstr e'
      tele' <- forM pvs $ \(p, v) -> do
        s <- abstractM abstr $ metaType v
        return $ TeleArg (metaHint v) p s
      return (Telescope tele', scope')
    normaliseScope h p c t s = do
      t' <- normalise t
      x <- forall h p t'
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
      (MkType m, _) | Just m == lzero -> return y'
      (_, MkType n) | Just n == rzero -> return x'
      (MkType m, MkType n) -> return $ MkType $ op m n
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

instantiateLetM
  :: (MonadFix m, MonadIO m, MonadVIX m)
  => LetRec Expr MetaA
  -> Scope LetVar Expr MetaA
  -> m AbstractM
instantiateLetM ds scope = mdo
  vs <- forMLet ds $ \h s t -> shared h Explicit (instantiateLet pure vs s) t
  return $ instantiateLet pure vs scope

etaReduce :: Expr v -> Maybe (Expr v)
etaReduce (Lam _ p _ (Scope (App e1scope p' (Var (B ())))))
  | p == p', Just e1' <- unusedScope $ Scope e1scope = Just e1'
etaReduce _ = Nothing
