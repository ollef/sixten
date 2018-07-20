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

type ExprFreeVar meta = FreeVar Plicitness (Expr meta)

type MonadNormalise meta m = (MonadIO m, MonadVIX m, MonadContext (ExprFreeVar meta) m, MonadError Error m, MonadFix m)

data Args meta m = Args
  { expandTypeReps :: !Bool
    -- ^ Should types be reduced to type representations (i.e. forget what the
    -- type is and only remember its representation)?
  , handleMetaVar :: !(meta -> m (Maybe (Closed (Expr meta))))
    -- ^ Allows whnf to try to solve unsolved class constraints when they're
    -- encountered.
  }

metaVarSolutionArgs :: MonadIO m => Args MetaVar m
metaVarSolutionArgs = Args
  { expandTypeReps = False
  , handleMetaVar = solution
  }

expandTypeRepsArgs :: MonadIO m => Args MetaVar m
expandTypeRepsArgs = metaVarSolutionArgs
  { expandTypeReps = True
  }

voidArgs :: Args Void m
voidArgs = Args
  { expandTypeReps = False
  , handleMetaVar = absurd
  }

-------------------------------------------------------------------------------
-- * Weak head normal forms
whnf
  :: MonadNormalise MetaVar m
  => CoreM
  -> m CoreM
whnf expr = whnf' metaVarSolutionArgs expr mempty

whnfExpandingTypeReps
  :: MonadNormalise MetaVar m
  => CoreM
  -> m CoreM
whnfExpandingTypeReps expr = whnf' expandTypeRepsArgs expr mempty

whnf'
  :: MonadNormalise meta m
  => Args meta m
  -> Expr meta (ExprFreeVar meta) -- ^ Expression to normalise
  -> [(Plicitness, Expr meta (ExprFreeVar meta))] -- ^ Arguments to the expression
  -> m (Expr meta (ExprFreeVar meta))
whnf' args expr exprs = indentLog $ do
  -- logMeta 40 "whnf e" $ apps expr exprs
  res <- normaliseBuiltins go expr exprs
  -- logMeta 40 "whnf res" res
  return res
  where
    go e@(Var FreeVar { varValue = Just e' }) es = do
      minlined <- normaliseDef whnf0 e' es
      case minlined of
        Nothing -> return $ apps e es
        Just (inlined, es') -> whnf' args inlined es'
    go e@(Var FreeVar { varValue = Nothing }) es = return $ apps e es
    go (Meta m mes) es = do
      sol <- handleMetaVar args m
      case sol of
        Nothing -> do
          mes' <- mapM (mapM whnf0) mes
          es' <- mapM (mapM whnf0) es
          return $ apps (Meta m mes') es'
        Just e' -> whnf' args (open e') $ toList mes ++ es
    go e@(Global g) es = do
      (d, _) <- definition g
      case d of
        ConstantDefinition Concrete e' -> do
          minlined <- normaliseDef whnf0 e' es
          case minlined of
            Nothing -> return $ apps e es
            Just (inlined, es') -> whnf' args inlined es'
        ConstantDefinition Abstract _ -> return $ apps e es
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
  :: MonadNormalise MetaVar m
  => CoreM
  -> m CoreM
normalise e = normalise' metaVarSolutionArgs e mempty

normalise'
  :: MonadNormalise meta m
  => Args meta m
  -> Expr meta (ExprFreeVar meta) -- ^ Expression to normalise
  -> [(Plicitness, Expr meta (ExprFreeVar meta))] -- ^ Arguments to the expression
  -> m (Expr meta (ExprFreeVar meta))
normalise' args expr exprs = do
  -- logMeta 40 "normalise e" $ apps expr exprs
  res <- normaliseBuiltins go expr exprs
  -- logMeta 40 "normalise res" res
  return res
  where
    go e@(Var FreeVar { varValue = Just e' }) es = do
      minlined <- normaliseDef normalise0 e' es
      case minlined of
        Nothing -> irreducible e es
        Just (inlined, es') -> normalise' args inlined es'
    go e@(Var FreeVar { varValue = Nothing }) es = irreducible e es
    go (Meta m mes) es = do
      msol <- handleMetaVar args m
      case msol of
        Nothing -> do
          mes' <- mapM (mapM normalise0) mes
          irreducible (Meta m mes') es
        Just e -> normalise' args (open e) $ toList mes ++ es
    go e@(Global g) es = do
      (d, _) <- definition g
      case d of
        ConstantDefinition Concrete e' -> do
          minlined <- normaliseDef normalise0 e' es
          case minlined of
            Nothing -> irreducible e es
            Just (inlined, es') -> normalise' args inlined es'
        ConstantDefinition Abstract _ -> irreducible e es
        DataDefinition _ rep
          | expandTypeReps args -> do
            minlined <- normaliseDef normalise0 rep es
            case minlined of
              Nothing -> irreducible e es
              Just (inlined, es') -> whnf' args inlined es'
          | otherwise -> irreducible e es
    go e@(Con _) es = irreducible e es
    go e@(Lit _) es = irreducible e es
    go (Pi h p t s) es = normaliseScope pi_ h p t s es
    -- TODO sharing
    go (Lam _ p1 _ s) ((p2, e):es) | p1 == p2 = normalise' args (Util.instantiate1 e s) es
    go (Lam h p t s) es = normaliseScope lam h p t s es
    go (App e1 p e2) es = normalise' args e1 ((p, e2) : es)
    go (Let ds scope) es = do
      e <- instantiateLetM ds scope
      normalise' args e es
    go (Case e brs retType) es = do
      e' <- normalise0 e
      case chooseBranch e' brs of
        Nothing -> do
          retType' <- normalise0 retType
          brs' <- case brs of
            ConBranches cbrs -> ConBranches
              <$> sequence
                [ normaliseConBranch qc tele s
                | ConBranch qc tele s <- cbrs
                ]
            LitBranches lbrs def -> LitBranches
              <$> sequence [LitBranch l <$> normalise0 br | LitBranch l br <- lbrs]
              <*> normalise0 def
          irreducible (Case e' brs' retType') es
        Just chosen -> normalise' args chosen es
    go (ExternCode c retType) es = do
      c' <- mapM normalise0 c
      retType' <- normalise0 retType
      irreducible (ExternCode c' retType') es

    irreducible e es = apps e <$> mapM (mapM normalise0) es

    normaliseConBranch qc tele scope = do
      vs <- forTeleWithPrefixM tele $ \h p s vs -> do
        t' <- withVars vs $ normalise0 $ instantiateTele pure vs s
        forall h p t'
      e' <- withVars vs $ normalise0 $ instantiateTele pure vs scope
      return $ conBranchTyped qc vs e'

    normaliseScope c h p t s es = do
      t' <- normalise0 t
      x <- forall h p t'
      e <- withVar x $ normalise0 $ Util.instantiate1 (pure x) s
      irreducible (c x e) es

    normalise0 e = normalise' args e mempty

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
normaliseBuiltins k e@(Global Builtin.MkTypeName) [(Explicit, x)] = do
  x' <- k x mempty
  case x' of
    Lit (Integer i) -> return $ MkType $ TypeRep.TypeRep i
    _ -> return $ App e Explicit x'
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
  => (Expr meta (ExprFreeVar meta) -> m (Expr meta (ExprFreeVar meta))) -- ^ How to normalise case scrutinees
  -> Expr meta (ExprFreeVar meta) -- ^ The definition
  -> [(Plicitness, Expr meta (ExprFreeVar meta))] -- ^ Arguments
  -> m (Maybe (Expr meta (ExprFreeVar meta), [(Plicitness, Expr meta (ExprFreeVar meta))]))
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
  => LetRec (Expr meta) (ExprFreeVar meta)
  -> Scope LetVar (Expr meta) (ExprFreeVar meta)
  -> m (Expr meta (ExprFreeVar meta))
instantiateLetM ds scope = mdo
  vs <- forMLet ds $ \h s t -> letVar h Explicit (instantiateLet pure vs s) t
  return $ instantiateLet pure vs scope

etaReduce :: Expr meta v -> Maybe (Expr meta v)
etaReduce (Lam _ p _ (Scope (App e1scope p' (Var (B ())))))
  | p == p', Just e1' <- unusedScope $ Scope e1scope = Just e1'
etaReduce _ = Nothing
