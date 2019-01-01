{-# LANGUAGE FlexibleContexts, OverloadedStrings, ViewPatterns #-}
module Elaboration.Constraint where

import Protolude

import Control.Lens
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Map as Map
import Data.Vector(Vector)

import Analysis.Simplify
import qualified Builtin.Names as Builtin
import Driver.Query
import Effect
import Elaboration.MetaVar
import Elaboration.MetaVar.Zonk
import Elaboration.Monad
import qualified Elaboration.Normalise as Normalise
import Elaboration.Subtype
import Elaboration.TypeOf
import Syntax
import Syntax.Core
import TypedFreeVar
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
trySolveConstraint m = inUpdatedContext (const mempty) $ do
  logShow "tc.constraint" "trySolveConstraint" $ metaId m
  withInstantiatedMetaType m $ \vs typ -> do
    typ' <- whnf typ
    case typ' of
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
                let sol = close (panic "trySolveConstraint not closed") $ lams vs matchingInstance
                solve m sol
                return $ Just sol
          candidates
            = [pure v | v <- toList vs, varData v == Constraint]
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
solveExprConstraints = bindMetas $ \m es -> do
  sol <- trySolveMetaVar m
  case sol of
    Nothing -> Meta m <$> traverse (traverse solveExprConstraints) es
    Just e -> solveExprConstraints $ betaApps (open e) es

solveDefConstraints
  :: Definition (Expr MetaVar) FreeV
  -> Elaborate (Definition (Expr MetaVar) FreeV)
solveDefConstraints (ConstantDefinition a e)
  = ConstantDefinition a <$> solveExprConstraints e
solveDefConstraints (DataDefinition (DataDef ps constrs) rep) =
  teleExtendContext ps $ \vs -> do
    constrs' <- forM constrs $ \(ConstrDef c s) -> do
      let e = instantiateTele pure vs s
      e' <- solveExprConstraints e
      return $ ConstrDef c e'

    rep' <- solveExprConstraints rep
    return $ DataDefinition (dataDef vs constrs') rep'

solveRecursiveDefConstraints
  :: Vector (FreeV, name, loc, Definition (Expr MetaVar) FreeV)
  -> Elaborate (Vector (FreeV, name, loc, Definition (Expr MetaVar) FreeV))
solveRecursiveDefConstraints defs = forM defs $ \(v, name, loc, def) -> do
  def' <- solveDefConstraints def
  _typ' <- solveExprConstraints $ varType v
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
      withInstantiatedMetaType m' $ \vs _ ->
        solve m'
          $ close (panic "mergeConstraintVars not closed")
          $ lams vs
          $ Meta m
          $ (\v -> (varData v, pure v)) <$> vs

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
