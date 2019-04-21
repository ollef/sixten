{-# LANGUAGE FlexibleContexts, OverloadedStrings, ViewPatterns #-}
module Elaboration.Constraint where

import Protolude

import Control.Lens
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Map as Map
import Data.Vector(Vector)

import qualified Builtin.Names as Builtin
import Driver.Query
import Effect
import qualified Effect.Context as Context
import Elaboration.MetaVar
import Elaboration.MetaVar.Zonk
import Elaboration.Monad
import qualified Elaboration.Normalise as Normalise
import Elaboration.Subtype
import Elaboration.TypeOf
import Elaboration.Unify
import Syntax
import Syntax.Core
import Util

trySolveMetaVar
  :: MonadElaborate m
  => MetaVar
  -> m (Maybe (Closed (Expr MetaVar)))
trySolveMetaVar m = do
  msol <- solution m
  case (msol, metaPlicitness m) of
    (Nothing, Constraint) -> trySolveConstraint m
    (Nothing, _) -> return Nothing
    (Just e, _) -> return $ Just e

trySolveConstraint
  :: MonadElaborate m
  => MetaVar
  -> m (Maybe (Closed (Expr MetaVar)))
trySolveConstraint m =
  modifyContext (const mempty) $
  maybe identity located (metaSourceLoc m) $ do
    logShow "tc.constraint" "trySolveConstraint" $ metaId m
    withInstantiatedMetaType m $ \vs typ -> do
      ctx <- getContext
      typ' <- whnf typ
      case typ' of
        Builtin.Equals _typ expr1 expr2 -> do
          runUnify (unify [] expr1 expr2) report
          openSol <- lams vs $ Builtin.Refl typ expr1 expr2
          let sol = close (panic "trySolveConstraint equals not closed") openSol
          solve m sol
          return $ Just sol
        (appsView -> (unSourceLoc -> Builtin.QGlobal className, _)) -> do
          -- Try subsumption on all instances of the class until a match is found
          mname <- view currentModule
          globalClassInstances <- fetchInstances className mname
          let
            go [] = do
              logCategory "tc.constraint" "No matching instance"
              return Nothing
            go (inst:candidates') = do
              instanceType <- typeOf inst
              mres <- untouchable
                $ runSubtype (Just . ($ inst) <$> subtypeE instanceType typ')
                $ \_err -> return Nothing
              case mres of
                Nothing -> go candidates'
                Just matchingInstance -> do
                  logMeta "tc.constraint" "Matching instance" $ zonk matchingInstance
                  logMeta "tc.constraint" "Matching instance typ" $ zonk typ'
                  openSol <- lams vs matchingInstance
                  let sol = close (panic "trySolveConstraint not closed") openSol
                  solve m sol
                  return $ Just sol
            candidates
              = [pure v | v <- toList vs, Context.lookupPlicitness v ctx == Constraint]
              <> [Global $ gname g | g <- HashSet.toList globalClassInstances]
          logShow "tc.constraint" "Candidates" $ length candidates
          go candidates
        _ -> do
          logMeta "tc.constraint" "Malformed" $ zonk typ'
          reportLocated "Malformed constraint" -- TODO error message
          return Nothing

solveExprConstraints
  :: CoreM
  -> Elaborate CoreM
solveExprConstraints = bindMetas' $ \m es -> do
  sol <- trySolveMetaVar m
  case sol of
    Nothing -> Meta m <$> traverse (traverse solveExprConstraints) es
    Just e -> do
      _e' <- solveExprConstraints $ open e
      return $ Meta m es
      -- solveExprConstraints $ betaApps (open e) es

solveDefConstraints
  :: Definition (Expr MetaVar) Var
  -> Elaborate (Definition (Expr MetaVar) Var)
solveDefConstraints (ConstantDefinition a e)
  = ConstantDefinition a <$> solveExprConstraints e
solveDefConstraints (DataDefinition (DataDef b ps constrs) rep) =
  teleExtendContext ps $ \vs -> do
    constrs' <- forM constrs $ \(ConstrDef c s) -> do
      let e = instantiateTele pure vs s
      e' <- solveExprConstraints e
      return $ ConstrDef c e'

    rep' <- solveExprConstraints rep
    dd <- dataDef b vs constrs'
    return $ DataDefinition dd rep'

solveRecursiveDefConstraints
  :: Vector (Var, name, loc, Definition (Expr MetaVar) Var)
  -> Elaborate (Vector (Var, name, loc, Definition (Expr MetaVar) Var))
solveRecursiveDefConstraints defs = forM defs $ \(v, name, loc, def) -> do
  def' <- solveDefConstraints def
  typ <- Context.lookupType v
  _typ' <- solveExprConstraints typ
  return (v, name, loc, def')

mergeConstraintVars
  :: HashSet MetaVar
  -> Elaborate (HashSet MetaVar) -- ^ The metavars that are still unsolved
mergeConstraintVars vars = do
  logShow "tc.constraint" "mergeConstraintVars" vars
  _ <- foldlM go mempty vars
  vars' <- filterMSet isUnsolved vars
  logShow "tc.constraint" "mergeConstraintVars result" vars'
  return vars'
  where
    go varTypes m@MetaVar { metaPlicitness = Constraint } = do
      let arity = metaArity m
      msol <- solution m
      case msol of
        Just _ -> return varTypes
        Nothing -> do
          typ <- zonk $ open $ metaType m
          let ctyp = close identity typ
          case Map.lookup (arity, ctyp) varTypes of
            Just m' -> do
              msol' <- solution m'
              case msol' of
                Just _ -> return $ Map.insert (arity, ctyp) m varTypes
                Nothing -> do
                  solveVar m m'
                  return varTypes
            Nothing -> return $ Map.insert (arity, ctyp) m varTypes
    go varTypes _ = return varTypes
    solveVar m m' =
      withInstantiatedMetaType m' $ \vs _ -> do
        ctx <- getContext
        e <- lams vs
          $ Meta m
          $ (\v -> (Context.lookupPlicitness v ctx, pure v)) <$> vs
        solve m' $ close (panic "mergeConstraintVars not closed") e

whnf :: MonadElaborate m => CoreM -> m CoreM
whnf e = Normalise.whnf' Normalise.Args
  { Normalise._expandTypeReps = False
  , Normalise._prettyExpr = prettyMeta <=< zonk
  , Normalise._handleMetaVar = trySolveMetaVar
  }
  e
  mempty

whnfExpandingTypeReps :: MonadElaborate m => CoreM -> m CoreM
whnfExpandingTypeReps e = Normalise.whnf' Normalise.Args
  { Normalise._expandTypeReps = True
  , Normalise._prettyExpr = prettyMeta <=< zonk
  , Normalise._handleMetaVar = trySolveMetaVar
  }
  e
  mempty
