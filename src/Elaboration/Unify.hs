{-# LANGUAGE FlexibleContexts, OverloadedStrings, ViewPatterns #-}
module Elaboration.Unify where

import Protolude hiding (TypeError)

import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector

import {-# SOURCE #-} Elaboration.Constraint
import Analysis.Simplify
import Effect
import Effect.Log as Log
import qualified Elaboration.Equal as Equal
import Elaboration.MetaVar
import Elaboration.MetaVar.Zonk
import Elaboration.Monad
import Elaboration.Normalise hiding (whnf)
import Elaboration.TypeOf
import Pretty
import Syntax
import Syntax.Core
import TypedFreeVar
import Util

type Unify = ExceptT Error Elaborate

runUnify :: Unify a -> (Error -> Elaborate a) -> Elaborate a
runUnify m handleError = do
  res <- runExceptT m
  case res of
    Left err -> handleError err
    Right f -> return f

unify :: [(CoreM, CoreM)] -> CoreM -> CoreM -> Unify ()
unify cxt expr1 expr2 = do
  logMeta "tc.unify" "unify t1" $ zonk expr1
  logMeta "tc.unify" "      t2" $ zonk expr2
  expr1' <- lift $ whnf expr1
  expr2' <- lift $ whnf expr2
  touchable <- lift getTouchable
  unify' ((expr1', expr2') : cxt) touchable expr1' expr2'

unify' :: [(CoreM, CoreM)] -> (MetaVar -> Bool) -> CoreM -> CoreM -> Unify ()
unify' cxt touchable expr1 expr2 = case (expr1, expr2) of
  (Pi h1 p1 t1 s1, Pi h2 p2 t2 s2) | p1 == p2 -> absCase (h1 <> h2) p1 t1 t2 s1 s2
  (Lam h1 p1 t1 s1, Lam h2 p2 t2 s2) | p1 == p2 -> absCase (h1 <> h2) p1 t1 t2 s1 s2
  -- Eta-expand
  (Lam h1 p1 t1 s1, _) -> do
    v <- forall h1 p1 t1
    withVar v $ unify cxt (instantiate1 (pure v) s1) (App expr2 p1 $ pure v)
  (_, Lam h p t s) -> do
    v <- forall h p t
    withVar v $ unify cxt (App expr1 p $ pure v) (instantiate1 (pure v) s)
  -- Eta-reduce
  (etaReduce -> Just expr1', _) -> unify cxt expr1' expr2
  (_, etaReduce -> Just expr2') -> unify cxt expr1 expr2'

  -- If we have 'unify (f xs) t', where 'f' is an existential, and 'xs' are
  -- distinct universally quantified variables, then 'f = \xs. t' is a most
  -- general solution (see Miller, Dale (1991) "A Logic programming...")
  (appsView -> (Meta m1 es1, es1'), appsView -> (Meta m2 es2, es2')) -> do
    let argVec1 = es1 <> toVector es1'
        argVec2 = es2 <> toVector es2'
    case (distinctVarView argVec1, distinctVarView argVec2) of
      _ | m1 == m2 -> sameVar m1 argVec1 argVec2
      (Just pvs, _) | touchable m1 -> solveVar unify m1 pvs expr2
      (_, Just pvs) | touchable m2 -> solveVar (flip . unify) m2 pvs expr1
      _ -> can'tUnify
  (appsView -> (Meta m es, es'), _)
    | touchable m
    , Just pvs <- distinctVarView (es <> toVector es')
    -> solveVar unify m pvs expr2
  (_, appsView -> (Meta m es, es'))
    | touchable m
    , Just pvs <- distinctVarView (es <> toVector es')
    -> solveVar (flip . unify) m pvs expr1
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
          logShow "tc.unify" "vs" (varId <$> vs)
          logMeta "tc.unify" ("solving t " <> show (metaId m)) $ zonk t
          logMeta "tc.unify" ("solving t' " <> show (metaId m)) $ zonk t'
          logMeta "tc.unify" ("solving lamt " <> show (metaId m)) $ zonk lamt
          logMeta "tc.unify" ("solving normlamt " <> show (metaId m)) $ zonk normLamt
          occurs cxt m normLamt
          case closed normLamt of
            Nothing -> can'tUnify
            Just closedLamt -> do
              lamtType <- typeOf normLamt
              recurse cxt (open $ metaType m) lamtType
              solve m $ close identity closedLamt
        Just c -> recurse cxt (apps (open c) $ second pure <$> pvs) t

    sameVar m pes1 pes2 = do
      when (Vector.length pes1 /= Vector.length pes2) $
        panic "sameVar mismatched length"

      let keepArg (p1, varView -> Just v1) (p2, varView -> Just v2) | p1 /= p2 || v1 /= v2 = False
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
              (close identity newMetaType'')
              (Vector.length vs')
              (metaSourceLoc m)
            let e = Meta m' $ (\v -> (varData v, pure v)) <$> vs'
                e' = lams vs e
            solve m $ close (panic "unify sameVar not closed") e'
            unify cxt expr1 expr2

    can'tUnify = do
      equal <- lift $ Equal.exec $ Equal.expr expr1 expr2
      unless equal typeMismatch

    typeMismatch = do
      printedCxt <- prettyContext cxt
      loc <- getCurrentLocation
      throwE $ TypeError
        ("Type mismatch" <> PP.line <>
          PP.vcat printedCxt)
          loc
          mempty

occurs
  :: [(CoreM, CoreM)]
  -> MetaVar
  -> CoreM
  -> Unify ()
occurs cxt mv expr = do
  mvs <- metaVars expr
  when (mv `HashSet.member` mvs) $ do
    printedMv <- prettyMetaVar mv
    expr' <- zonk expr
    printedExpr <- prettyMeta expr'
    printedCxt <- prettyContext cxt
    loc <- getCurrentLocation
    throwE $ TypeError
      ("Cannot construct the infinite type"
      <> PP.line
      <> PP.vcat
        ([ dullBlue printedMv
        , "="
        , dullBlue printedExpr
        , ""
        , "while trying to unify"
        ] ++ printedCxt))
        loc
        mempty

prettyContext :: [(CoreM, CoreM)] -> Unify [PP.Doc AnsiStyle]
prettyContext cxt = do
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
  return $ intercalate ["", "while trying to unify"] explanation

prune :: HashSet FreeV -> CoreM -> Unify CoreM
prune allowed expr = Log.indent $ do
  logMeta "tc.unify.prune" "prune expr" $ zonk expr
  logShow "tc.unify.prune" "prune allowed" $ pretty <$> toList allowed
  res <- inUpdatedContext (const mempty) $ bindMetas go expr
  logMeta "tc.unify.prune" "prune res" $ zonk res
  return res
  where
    go m es = do
      -- logShow 30 "prune" $ metaId m
      sol <- solution m
      case sol of
        Just e ->
          bindMetas go $ betaApps (open e) es
        Nothing -> do
          es' <- lift $ mapM (mapM whnf) es
          localAllowed <- toHashSet <$> lift getLocalVars
          case distinctVarView es' of
            Nothing ->
              return $ Meta m es'
            Just pvs
              | Vector.length vs' == Vector.length vs ->
                return $ Meta m es'
              | otherwise -> do
                newMetaType <- prune (toHashSet vs') mType
                newMetaType' <- normalise $ pis vs' newMetaType
                logShow "tc.prune" "prune m" $ metaId m
                logMeta "tc.prune" "prune metaType" $ zonk (open $ metaType m :: CoreM)
                logMeta "tc.prune" "prune newMetaType'" $ zonk newMetaType'
                logShow "tc.prune" "prune vs" $ varId <$> vs
                logShow "tc.prune" "prune vs'" $ varId <$> vs'
                case closed newMetaType' of
                  Nothing -> do
                    logShow "tc.prune" "prune not closed newMetaType'" ()
                    return $ Meta m es'
                  Just newMetaType'' -> do
                    m' <- explicitExists
                      (metaHint m)
                      (metaPlicitness m)
                      (close identity newMetaType'')
                      (Vector.length vs')
                      (metaSourceLoc m)
                    let e = Meta m' $ (\v -> (varData v, pure v)) <$> vs'
                        e' = lams plicitVs e
                    -- logShow 30 "prune varTypes" =<< mapM (prettyMeta . varType) vs
                    -- logShow 30 "prune vs'" $ varId <$> vs'
                    -- logShow 30 "prune varTypes'" =<< mapM (prettyMeta . varType) vs'
                    logMeta "tc.prune" "prune e'" $ zonk e'
                    case closed e' of
                      Nothing -> do
                        logShow "tc.prune" "prune not closed e'" ()
                        return $ Meta m es'
                      Just closedSol -> do
                        logMeta "tc.prune" "prune closed" $ zonk closedSol
                        solve m $ close identity closedSol
                        return e
              | otherwise -> return $ Meta m es'
              where
                vs = snd <$> pvs
                vs' = Vector.filter (`HashSet.member` (allowed <> localAllowed)) vs
                plicitVs = (\(p, v) -> v { varData = p }) <$> pvs
                Just mType = typeApps (open $ metaType m) es
