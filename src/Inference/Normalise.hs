{-# LANGUAGE ConstraintKinds, FlexibleContexts, MonadComprehensions, ViewPatterns, RecursiveDo #-}
module Inference.Normalise where

import Control.Monad.Except
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Vector as Vector
import Data.Void

import qualified Builtin.Names as Builtin
import Inference.MetaVar
import Inference.Monad
import MonadContext
import Syntax
import Syntax.Abstract
import TypedFreeVar
import TypeRep(TypeRep)
import qualified TypeRep
import Util
import VIX

type MonadNormalise m = (MonadIO m, MonadVIX m, MonadContext FreeV m, MonadError Error m, MonadFix m)

-------------------------------------------------------------------------------
-- * Weak head normal forms
whnf
  :: MonadNormalise m
  => AbstractM
  -> m AbstractM
whnf = whnf' WhnfArgs
  { expandTypeReps = False
  , handleMetaVar = \m -> do
    sol <- solution m
    case sol of
      Left _ -> return Nothing
      Right e -> return $ Just e
  }

whnfExpandingTypeReps
  :: MonadNormalise m
  => AbstractM
  -> m AbstractM
whnfExpandingTypeReps = whnf' WhnfArgs
  { expandTypeReps = True
  , handleMetaVar = \m -> do
    sol <- solution m
    case sol of
      Left _ -> return Nothing
      Right e -> return $ Just e
  }

data WhnfArgs m = WhnfArgs
  { expandTypeReps :: !Bool
    -- ^ Should types be reduced to type representations (i.e. forget what the
    -- type is and only remember its representation)?
  , handleMetaVar :: !(MetaVar -> m (Maybe (Expr MetaVar Void)))
    -- ^ Allows whnf to try to solve unsolved class constraints when they're
    -- encountered.
  }

whnf'
  :: MonadNormalise m
  => WhnfArgs m
  -> AbstractM
  -> m AbstractM
whnf' args expr = indentLog $ do
  logMeta 40 "whnf e" expr
  res <- uncurry go $ appsView expr
  logMeta 40 "whnf res" res
  return res
  where
    go f [] = whnfInner args f
    go f es@((p, e):es') = do
      f' <- whnfInner args f
      case f' of
        Lam _ p' _ s | p == p' -> do
          -- TODO sharing?
          go (Util.instantiate1 e s) es'
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
          expr' -> return expr'

whnfInner
  :: MonadNormalise m
  => WhnfArgs m
  -> AbstractM
  -> m AbstractM
whnfInner args expr = case expr of
  Var (FreeVar { varValue = Just e }) -> whnf' args e
  Var (FreeVar { varValue = Nothing }) -> return expr
  Meta m es -> do
    sol <- handleMetaVar args m
    case sol of
      Nothing -> return expr
      Just e -> whnf' args $ apps (vacuous e) es
  Global g -> do
    (d, _) <- definition g
    case d of
      Definition Concrete _ e -> whnf' args e
      DataDefinition _ e | expandTypeReps args -> whnf' args e
      _ -> return expr
  Con _ -> return expr
  Lit _ -> return expr
  Pi {} -> return expr
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
  :: MonadNormalise m
  => AbstractM
  -> m AbstractM
normalise expr = do
  logMeta 40 "normalise e" expr
  res <- indentLog $ case expr of
    Var (FreeVar { varValue = Just e }) -> normalise e
    Var (FreeVar { varValue = Nothing }) -> return expr
    Meta m es -> traverseMetaSolution normalise m es
    Global g -> do
      (d, _) <- definition g
      case d of
        Definition Concrete _ e -> normalise e
        _ -> return expr
    Con _ -> return expr
    Lit _ -> return expr
    Pi n p a s -> normaliseScope n p (Pi n p) a s
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
        -- TODO sharing?
        Lam _ p' _ s | p == p' ->
          normalise $ Util.instantiate1 e2 s
        _ -> do
          e2' <- normalise e2
          return $ App e1' p e2'
    Let ds scope -> do
      e <- instantiateLetM ds scope
      normalise e
    Case e brs retType -> do
      e' <- normalise e
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
  logMeta 40 "normalise res" res
  return res
  where
    normaliseTelescope tele scope = do
      vs <- forTeleWithPrefixM tele $ \h p s vs -> do
        t' <- normalise $ instantiateTele pure vs s
        forall h p t'

      let abstr = teleAbstraction vs
      e' <- withVars vs $ normalise $ instantiateTele pure vs scope
      let scope' = abstract abstr e'
      tele' <- forM vs $ \v -> do
        let s = abstract abstr $ varType v
        return $ TeleArg (varHint v) (varData v) s
      return (Telescope tele', scope')
    normaliseScope h p c t s = do
      t' <- normalise t
      x <- forall h p t'
      ns <- withVar x $ normalise $ Util.instantiate1 (pure x) s
      return $ c t' $ abstract1 x ns

binOp
  :: Monad m
  => Maybe Integer
  -> Maybe Integer
  -> (Integer -> Integer -> Integer)
  -> (Expr meta v -> Expr meta v -> Expr meta v)
  -> (Expr meta v -> m (Expr meta v))
  -> Expr meta v
  -> Expr meta v
  -> m (Expr meta v)
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
  -> (Expr meta v -> Expr meta v -> Expr meta v)
  -> (Expr meta v -> m (Expr meta v))
  -> Expr meta v
  -> Expr meta v
  -> m (Expr meta v)
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
  => Expr meta v
  -> Branches Plicitness (Expr meta) v
  -> Expr meta v
  -> (Expr meta v -> m (Expr meta v))
  -> m (Expr meta v)
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
  => LetRec (Expr MetaVar) FreeV
  -> Scope LetVar (Expr MetaVar) FreeV
  -> m AbstractM
instantiateLetM ds scope = mdo
  vs <- forMLet ds $ \h s t -> letVar h Explicit (instantiateLet pure vs s) t
  return $ instantiateLet pure vs scope

etaReduce :: Expr meta v -> Maybe (Expr meta v)
etaReduce (Lam _ p _ (Scope (App e1scope p' (Var (B ())))))
  | p == p', Just e1' <- unusedScope $ Scope e1scope = Just e1'
etaReduce _ = Nothing
