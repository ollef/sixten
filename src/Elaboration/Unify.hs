{-# LANGUAGE FlexibleContexts, OverloadedStrings, ViewPatterns #-}
module Elaboration.Unify where

import Control.Monad.Except
import Data.Bifunctor
import Data.Hashable
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.List
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector

import {-# SOURCE #-} Elaboration.Constraint
import Analysis.Simplify
import qualified Elaboration.Equal as Equal
import Elaboration.MetaVar
import Elaboration.MetaVar.Zonk
import Elaboration.Monad
import Elaboration.Normalise hiding (whnf)
import Elaboration.TypeOf
import MonadContext
import Pretty
import Syntax
import Syntax.Core
import TypedFreeVar
import Util
import VIX

unify :: [(CoreM, CoreM)] -> CoreM -> CoreM -> Infer ()
unify cxt type1 type2 = do
  logMeta 30 "unify t1" type1
  logMeta 30 "      t2" type2
  type1' <- whnf type1
  type2' <- whnf type2
  touchable <- getTouchable
  unify' ((type1', type2') : cxt) touchable type1' type2'

unify' :: [(CoreM, CoreM)] -> (MetaVar -> Bool) -> CoreM -> CoreM -> Infer ()
unify' cxt touchable type1 type2 = case (type1, type2) of
  (Pi h1 p1 t1 s1, Pi h2 p2 t2 s2) | p1 == p2 -> absCase (h1 <> h2) p1 t1 t2 s1 s2
  (Lam h1 p1 t1 s1, Lam h2 p2 t2 s2) | p1 == p2 -> absCase (h1 <> h2) p1 t1 t2 s1 s2
  -- Eta-expand
  (Lam h p t s, _) -> do
    v <- forall h p t
    withVar v $ unify cxt (instantiate1 (pure v) s) (App type2 p $ pure v)
  (_, Lam h p t s) -> do
    v <- forall h p t
    withVar v $ unify cxt (App type1 p $ pure v) (instantiate1 (pure v) s)
  -- Eta-reduce
  (etaReduce -> Just type1', _) -> unify cxt type1' type2
  (_, etaReduce -> Just type2') -> unify cxt type1 type2'

  -- If we have 'unify (f xs) t', where 'f' is an existential, and 'xs' are
  -- distinct universally quantified variables, then 'f = \xs. t' is a most
  -- general solution (see Miller, Dale (1991) "A Logic programming...")
  (appsView -> (Meta m1 es1, es1'), appsView -> (Meta m2 es2, es2')) -> do
    let argVec1 = es1 <> toVector es1'
        argVec2 = es2 <> toVector es2'
    case (distinctVars argVec1, distinctVars argVec2) of
      _ | m1 == m2 -> sameVar m1 argVec1 argVec2
      (Just pvs, _) | touchable m1 -> solveVar unify m1 pvs type2
      (_, Just pvs) | touchable m2 -> solveVar (flip . unify) m2 pvs type1
      _ -> can'tUnify
  (appsView -> (Meta m es, es'), _)
    | touchable m
    , Just pvs <- distinctVars (es <> toVector es')
    -> solveVar unify m pvs type2
  (_, appsView -> (Meta m es, es'))
    | touchable m
    , Just pvs <- distinctVars (es <> toVector es')
    -> solveVar (flip . unify) m pvs type1
  -- Since we've already tried reducing the application, we can only hope to
  -- unify it pointwise.
  (App e1 p1 e1', App e2 p2 e2') | p1 == p2 -> do
    unify cxt e1  e2
    unify cxt e1' e2'
  _ -> can'tUnify
  where
    absCase h p t1 t2 s1 s2 = do
      unify cxt t1 t2
      v <- forall h p t1
      withVar v $ unify cxt (instantiate1 (pure v) s1) (instantiate1 (pure v) s2)

    solveVar recurse m pvs t = do
      msol <- solution m
      case msol of
        Nothing -> do
          let vs = snd <$> pvs
              plicitVs = (\(p, v) -> v { varData = p }) <$> pvs
          t' <- prune (toHashSet vs) t
          let lamt = lams plicitVs t'
          normLamt <- normalise lamt
          logShow 30 "vs" (varId <$> vs)
          logMeta 30 ("solving t " <> show (metaId m)) t
          logMeta 30 ("solving t' " <> show (metaId m)) t'
          logMeta 30 ("solving lamt " <> show (metaId m)) lamt
          logMeta 30 ("solving normlamt " <> show (metaId m)) normLamt
          occurs cxt m normLamt
          case closed normLamt of
            Nothing -> can'tUnify
            Just closedLamt -> do
              lamtType <- typeOf normLamt
              recurse cxt (open $ metaType m) lamtType
              solve m $ close id closedLamt
        Just c -> recurse cxt (apps (open c) $ second pure <$> pvs) t

    sameVar m pes1 pes2 = do
      when (Vector.length pes1 /= Vector.length pes2) $
        error "sameVar mismatched length"

      let keepArg (isVar -> Just v1) (isVar -> Just v2) | v1 /= v2 = False
          keepArg _ _ = True
          keep = Vector.zipWith keepArg pes1 pes2
      if and keep then
        -- If we keep all arguments we can't make any progress without delayed
        -- constraint solving other than checking for equality.
        can'tUnify
      else do
        (vs, typ) <- instantiatedMetaType' (Vector.length pes1) m
        let vs' = snd <$> Vector.filter fst (Vector.zip keep vs)
        prunedType <- prune (toHashSet vs') typ
        let newMetaType = pis vs' prunedType
        newMetaType' <- normalise newMetaType

        case closed newMetaType' of
          Nothing -> can'tUnify
          Just newMetaType'' -> do
            m' <- explicitExists
              (metaHint m)
              (metaPlicitness m)
              (close id newMetaType'')
              (Vector.length vs')
              (metaSourceLoc m)
            let e = Meta m' $ (\v -> (varData v, pure v)) <$> vs'
                e' = lams vs e
            solve m $ close (error "unify sameVar not closed") e'
            unify cxt type1 type2

    can'tUnify = do
      equal <- Equal.exec $ Equal.expr type1 type2
      unless equal typeMismatch

    typeMismatch = do
      explanation <- forM cxt $ \(t1, t2) -> do
        t1' <- zonk t1
        t2' <- zonk t2
        actual <- prettyMeta t1'
        expect <- prettyMeta t2'
        return
          [ ""
          , bold "Inferred:" PP.<+> red actual
          , bold "Expected:" PP.<+> dullGreen expect
          ]
      throwLocated
        $ "Type mismatch" <> PP.line <>
          PP.vcat (intercalate ["", "while trying to unify"] explanation)

occurs
  :: [(CoreM, CoreM)]
  -> MetaVar
  -> CoreM
  -> Infer ()
occurs cxt mv expr = do
  mvs <- metaVars expr
  when (mv `HashSet.member` mvs) $ do
    explanation <- forM cxt $ \(t1, t2) -> do
      t1' <- zonk t1
      t2' <- zonk t2
      actual <- prettyMeta t1'
      expect <- prettyMeta t2'
      return
        [ ""
        , bold "Inferred:" PP.<+> red actual
        , bold "Expected:" PP.<+> dullGreen expect
        ]
    printedMv <- prettyMetaVar mv
    expr' <- zonk expr
    printedExpr <- prettyMeta expr'
    throwLocated
      $ "Cannot construct the infinite type"
      <> PP.line
      <> PP.vcat
        ([ dullBlue printedMv
        , "="
        , dullBlue printedExpr
        , ""
        , "while trying to unify"
        ] ++ intercalate ["", "while trying to unify"] explanation)

prune :: HashSet FreeV -> CoreM -> Infer CoreM
prune allowed expr = indentLog $ do
  logMeta 35 "prune expr" expr
  res <- inUpdatedContext (const mempty) $ bindMetas go expr
  logMeta 35 "prune res" res
  return res
  where
    go m es = do
      -- logShow 30 "prune" $ metaId m
      sol <- solution m
      case sol of
        Just e -> do
          -- VIX.logShow 30 "prune solved" ()
          bindMetas go $ betaApps (open e) es
        Nothing -> do
          es' <- mapM (mapM whnf) es
          localAllowed <- toHashSet <$> localVars
          case distinctVars es' of
            Nothing -> do
              -- VIX.logShow 30 "prune not distinct" ()
              return $ Meta m es'
            Just pvs
              | Vector.length vs' == Vector.length vs -> do
                -- VIX.logShow 30 "prune nothing to do" ()
                return $ Meta m es'
              | otherwise -> do
                newMetaType' <- prune (toHashSet vs') mType
                newMetaType'' <- normalise $ pis vs' newMetaType'
                logMeta 30 "prune newMetaType'" newMetaType''
                logShow 30 "prune vs" $ varId <$> vs
                -- logShow 30 "prune vs'" $ varId <$> vs'
                case closed newMetaType'' of
                  Nothing -> return $ Meta m es'
                  Just newMetaType''' -> do
                    m' <- explicitExists
                      (metaHint m)
                      (metaPlicitness m)
                      (close id newMetaType''')
                      (Vector.length vs')
                      (metaSourceLoc m)
                    let e = Meta m' $ (\v -> (varData v, pure v)) <$> vs'
                        e' = lams plicitVs e
                    -- logShow 30 "prune varTypes" =<< mapM (prettyMeta . varType) vs
                    -- logShow 30 "prune vs'" $ varId <$> vs'
                    -- logShow 30 "prune varTypes'" =<< mapM (prettyMeta . varType) vs'
                    logMeta 30 "prune e'" e'
                    case closed e' of
                      Nothing -> do
                        logShow 30 "prune not closed" ()
                        return $ Meta m es'
                      Just closedSol -> do
                        logMeta 30 "prune closed" closedSol
                        solve m $ close id closedSol
                        return e
              | otherwise -> return $ Meta m es'
              where
                vs = snd <$> pvs
                vs' = Vector.filter (`HashSet.member` (allowed <> localAllowed)) vs
                plicitVs = (\(p, v) -> v { varData = p }) <$> pvs
                Just mType = typeApps (open $ metaType m) es

distinctVars :: (Eq v, Hashable v, Traversable t) => t (p, Expr m v) -> Maybe (t (p, v))
distinctVars es = case traverse isVar es of
  Just es' | distinct (snd <$> es') -> Just es'
  _ -> Nothing

isVar :: (p, Expr m a) -> Maybe (p, a)
isVar (p, Var v) = Just (p, v)
isVar _ = Nothing

distinct :: (Foldable t, Hashable a, Eq a) => t a -> Bool
distinct es = HashSet.size (toHashSet es) == length es
