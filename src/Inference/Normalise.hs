{-# LANGUAGE ConstraintKinds, FlexibleContexts, MonadComprehensions, ViewPatterns, RecursiveDo #-}
module Inference.Normalise where

import Control.Monad.Except
import Data.Foldable
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Vector as Vector
import Data.Void

import qualified Builtin.Names as Builtin
import Inference.MetaVar
import Inference.Monad
import MonadContext
import Syntax
import Syntax.Core
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
  => CoreM
  -> m CoreM
whnf expr = whnf' WhnfArgs
  { expandTypeReps = False
  , handleMetaVar = \m -> do
    sol <- solution m
    case sol of
      Left _ -> return Nothing
      Right e -> return $ Just e
  }
  expr
  mempty

whnfExpandingTypeReps
  :: MonadNormalise m
  => CoreM
  -> m CoreM
whnfExpandingTypeReps expr = whnf' WhnfArgs
  { expandTypeReps = True
  , handleMetaVar = \m -> do
    sol <- solution m
    case sol of
      Left _ -> return Nothing
      Right e -> return $ Just e
  }
  expr
  mempty

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
  -> CoreM -- ^ Expression to normalise
  -> [(Plicitness, CoreM)] -- ^ Arguments to the expression
  -> m CoreM
whnf' args expr exprs = indentLog $ do
  logMeta 40 "whnf e" expr
  res <- normaliseBuiltins go expr exprs
  logMeta 40 "whnf res" res
  return res
  where
    go e@(Var FreeVar { varValue = Just e' }) es = do
      minlined <- normaliseDef whnf0 e' es
      case minlined of
        Nothing -> return $ apps e es
        Just (inlined, es') -> whnf' args inlined es'
    go e@(Var FreeVar { varValue = Nothing }) es = return $ apps e es
    go e@(Meta m mes) es = do
      sol <- handleMetaVar args m
      case sol of
        Nothing -> return $ apps e es
        Just e' -> whnf' args (vacuous e') $ toList mes ++ es
    go e@(Global g) es = do
      (d, _) <- definition g
      case d of
        Definition Concrete _ e' -> do
          minlined <- normaliseDef whnf0 e' es
          case minlined of
            Nothing -> return $ apps e es
            Just (inlined, es') -> whnf' args inlined es'
        Definition Abstract _ _ -> return $ apps e es
        DataDefinition _ rep
          | expandTypeReps args -> do
            minlined <- normaliseDef whnf0 rep es
            case minlined of
              Nothing -> return $ apps e es
              Just (inlined, es') -> whnf' args inlined es'
          | otherwise -> return $ apps e es
    go e@(Con _) es = return $ apps e es
    go e@(Lit _) es = return $ apps e es
    go e@Pi {} es = return $ apps e es
    go (Lam _ p1 _ s) ((p2, e):es) | p1 == p2 = whnf' args (Util.instantiate1 e s) es
    go e@Lam {} es = return $ apps e es
    go (App e1 p e2) es = whnf' args e1 $ (p, e2) : es
    go (Let ds scope) es = do
      e <- instantiateLetM ds scope
      whnf' args e es
    go (Case e brs retType) es = do
      e' <- whnf0 e
      case chooseBranch e' brs of
        Nothing -> Case e' brs <$> whnf0 retType
        Just chosen -> whnf' args chosen es
    go (ExternCode c retType) es = do
      c' <- mapM whnf0 c
      retType' <- whnf0 retType
      return $ apps (ExternCode c' retType') es

    whnf0 e = whnf' args e mempty

normalise
  :: MonadNormalise m
  => CoreM
  -> m CoreM
normalise e = normalise' e mempty

normalise'
  :: MonadNormalise m
  => CoreM -- ^ Expression to normalise
  -> [(Plicitness, CoreM)] -- ^ Arguments to the expression
  -> m CoreM
normalise' expr exprs = do
  logMeta 40 "normalise e" expr
  res <- normaliseBuiltins go expr exprs
  logMeta 40 "normalise res" res
  return res
  where
    go
      :: MonadNormalise m
      => CoreM
      -> [(Plicitness, CoreM)]
      -> m CoreM
    go e@(Var FreeVar { varValue = Just e' }) es = do
      minlined <- normaliseDef normalise e' es
      case minlined of
        Nothing -> irreducible e es
        Just (inlined, es') -> normalise' inlined es'
    go e@(Var FreeVar { varValue = Nothing }) es = irreducible e es
    go (Meta m mes) es = do
      sol <- solution m
      case sol of
        Left _ -> do
          mes' <- mapM (mapM normalise) mes
          irreducible (Meta m mes') es
        Right e -> normalise' (vacuous e) $ toList mes ++ es
    go e@(Global g) es = do
      (d, _) <- definition g
      case d of
        Definition Concrete _ e' -> do
          minlined <- normaliseDef normalise e' es
          case minlined of
            Nothing -> irreducible e es
            Just (inlined, es') -> normalise' inlined es'
        Definition Abstract _ _ -> irreducible e es
        DataDefinition {} -> irreducible e es
    go e@(Con _) es = irreducible e es
    go e@(Lit _) es = irreducible e es
    go (Pi h p t s) es = normaliseScope pi_ h p t s es
    -- TODO sharing
    go (Lam _ p1 _ s) ((p2, e):es) | p1 == p2 = normalise' (Util.instantiate1 e s) es
    go (Lam h p t s) es = normaliseScope lam h p t s es
    go (App e1 p e2) es = normalise' e1 ((p, e2) : es)
    go (Let ds scope) es = do
      e <- instantiateLetM ds scope
      normalise' e es
    go (Case e brs retType) es = do
      e' <- normalise e
      case chooseBranch e' brs of
        Nothing -> do
          retType' <- normalise retType
          brs' <- case brs of
            ConBranches cbrs -> ConBranches
              <$> sequence
                [ normaliseConBranch qc tele s
                | ConBranch qc tele s <- cbrs
                ]
            LitBranches lbrs def -> LitBranches
              <$> sequence [LitBranch l <$> normalise br | LitBranch l br <- lbrs]
              <*> normalise def
          irreducible (Case e' brs' retType') es
        Just chosen -> normalise' chosen es
    go (ExternCode c retType) es = do
      c' <- mapM normalise c
      retType' <- normalise retType
      irreducible (ExternCode c' retType') es

    irreducible e es = apps e <$> mapM (mapM normalise) es

    normaliseConBranch qc tele scope = do
      vs <- forTeleWithPrefixM tele $ \h p s vs -> do
        t' <- normalise $ instantiateTele pure vs s
        forall h p t'
      e' <- withVars vs $ normalise $ instantiateTele pure vs scope
      return $ conBranchTyped qc vs e'

    normaliseScope c h p t s es = do
      t' <- normalise t
      x <- forall h p t'
      e <- withVar x $ normalise $ Util.instantiate1 (pure x) s
      irreducible (c x e) es

normaliseBuiltins
  :: Monad m
  => (Expr meta v -> [(Plicitness, Expr meta v)] -> m (Expr meta v))
  -> Expr meta v
  -> [(Plicitness, Expr meta v)]
  -> m (Expr meta v)
normaliseBuiltins k (Global Builtin.ProductTypeRepName) [(Explicit, x), (Explicit, y)] = typeRepBinOp
  (Just TypeRep.UnitRep) (Just TypeRep.UnitRep)
  TypeRep.product Builtin.ProductTypeRep
  k x y
normaliseBuiltins k (Global Builtin.SumTypeRepName) [(Explicit, x), (Explicit, y)] = typeRepBinOp
  (Just TypeRep.UnitRep) (Just TypeRep.UnitRep)
  TypeRep.sum Builtin.SumTypeRep
  k x y
normaliseBuiltins k (Global Builtin.SubIntName) [(Explicit, x), (Explicit, y)] =
  binOp Nothing (Just 0) (-) Builtin.SubInt k x y
normaliseBuiltins k (Global Builtin.AddIntName) [(Explicit, x), (Explicit, y)] =
  binOp (Just 0) (Just 0) (+) Builtin.AddInt k x y
normaliseBuiltins k (Global Builtin.MaxIntName) [(Explicit, x), (Explicit, y)] =
  binOp (Just 0) (Just 0) max Builtin.MaxInt k x y
normaliseBuiltins k e es = k e es

binOp
  :: Monad m
  => Maybe Integer
  -> Maybe Integer
  -> (Integer -> Integer -> Integer)
  -> (Expr meta v -> Expr meta v -> Expr meta v)
  -> (Expr meta v -> [(Plicitness, Expr meta v)] -> m (Expr meta v))
  -> Expr meta v
  -> Expr meta v
  -> m (Expr meta v)
binOp lzero rzero op cop k x y = do
  x' <- normaliseBuiltins k x mempty
  y' <- normaliseBuiltins k y mempty
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
  -> (Expr meta v -> [(Plicitness, Expr meta v)] -> m (Expr meta v))
  -> Expr meta v
  -> Expr meta v
  -> m (Expr meta v)
typeRepBinOp lzero rzero op cop k x y = do
  x' <- normaliseBuiltins k x mempty
  y' <- normaliseBuiltins k y mempty
  case (x', y') of
    (MkType m, _) | Just m == lzero -> return y'
    (_, MkType n) | Just n == rzero -> return x'
    (MkType m, MkType n) -> return $ MkType $ op m n
    _ -> return $ cop x' y'

chooseBranch
  :: Expr meta v
  -> Branches Plicitness (Expr meta) v
  -> Maybe (Expr meta v)
chooseBranch (Lit l) (LitBranches lbrs def) = Just chosenBranch
  where
    chosenBranch = head $ [br | LitBranch l' br <- NonEmpty.toList lbrs, l == l'] ++ [def]
chooseBranch (appsView -> (Con qc, args)) (ConBranches cbrs) =
  Just $ instantiateTele snd (Vector.drop (Vector.length argsv - numConArgs) argsv) chosenBranch
  where
    argsv = Vector.fromList args
    (numConArgs, chosenBranch) = case [(teleLength tele, br) | ConBranch qc' tele br <- cbrs, qc == qc'] of
      [br] -> br
      _ -> error "Normalise.chooseBranch"
chooseBranch _ _ = Nothing

-- | Definition normalisation heuristic:
--
-- If a definition is of the form `f = \xs. cases`, we inline `f` during the
-- normalisation of `f es` if:
--
-- The application is saturated, i.e. `length es >= length xs`, and the
-- (possibly nested) case expressions `cases` reduce to something that doesn't
-- start with a case.
--
-- This is done to avoid endlessly unfolding recursive definitions. It means
-- that it's possible to miss some definitional equalities, but this is
-- hopefully rarely the case in practice.
normaliseDef
  :: Monad m
  => (CoreM -> m CoreM) -- ^ How to normalise case scrutinees
  -> CoreM -- ^ The definition
  -> [(Plicitness, CoreM)] -- ^ Arguments
  -> m (Maybe (CoreM, [(Plicitness, CoreM)]))
  -- ^ The definition body applied to some arguments and any arguments that are still left
normaliseDef norm = lambdas
  where
    lambdas (Lam _ p2 _ s) ((p1, e):es) | p1 == p2 = lambdas (instantiate1 e s) es
    lambdas Lam {} [] = return Nothing
    lambdas e es = do
      mresult <- cases e
      return $ flip (,) es <$> mresult
    cases (Case e brs _retType) = do
      e' <- norm e
      case chooseBranch e' brs of
        Nothing -> return Nothing
        Just chosen -> cases chosen
    cases e = return $ Just e

instantiateLetM
  :: (MonadFix m, MonadIO m, MonadVIX m)
  => LetRec (Expr MetaVar) FreeV
  -> Scope LetVar (Expr MetaVar) FreeV
  -> m CoreM
instantiateLetM ds scope = mdo
  vs <- forMLet ds $ \h s t -> letVar h Explicit (instantiateLet pure vs s) t
  return $ instantiateLet pure vs scope

etaReduce :: Expr meta v -> Maybe (Expr meta v)
etaReduce (Lam _ p _ (Scope (App e1scope p' (Var (B ())))))
  | p == p', Just e1' <- unusedScope $ Scope e1scope = Just e1'
etaReduce _ = Nothing
