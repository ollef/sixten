{-# LANGUAGE FlexibleContexts, OverloadedStrings, ViewPatterns #-}
module Elaboration.Constraint where

import Control.Monad.Except
import Data.Bifunctor
import Data.Foldable
import Data.HashSet(HashSet)
import qualified Data.Map as Map
import Data.Maybe
import Data.Vector(Vector)
import Data.Void

import Analysis.Simplify
import Elaboration.MetaVar
import Elaboration.MetaVar.Zonk
import Elaboration.Monad
import qualified Elaboration.Normalise as Normalise
import Elaboration.Subtype
import MonadContext
import MonadLog
import Syntax
import Syntax.Core
import TypedFreeVar
import Util
import VIX

trySolveMetaVar
  :: MetaVar
  -> Elaborate (Maybe (Closed (Expr MetaVar)))
trySolveMetaVar m = do
  msol <- solution m
  case (msol, metaPlicitness m) of
    (Nothing, Constraint) -> trySolveConstraint m
    (Nothing, _) -> return Nothing
    (Just e, _) -> return $ Just e

trySolveConstraint
  :: MetaVar
  -> Elaborate (Maybe (Closed (Expr MetaVar)))
trySolveConstraint m = inUpdatedContext (const mempty) $ do
  logShow 25 "trySolveConstraint" $ metaId m
  (vs, typ) <- instantiatedMetaType m
  withVars vs $ do
    typ' <- whnf typ
    case typ' of
      (appsView -> (Global className, _)) -> do
        -- Try subsumption on all instances of the class until a match is found
        globalClassInstances <- instances className
        let candidates = [(Global g, bimap absurd absurd t) | (g, t) <- globalClassInstances]
              <> [(pure v, varType v) | v <- toList vs, varData v == Constraint]
        matchingInstances <- forM candidates $ \(inst, instanceType) -> tryMaybe $ do
          logMeta 35 "candidate instance" inst
          logMeta 35 "candidate instance type" instanceType
          f <- untouchable $ subtype instanceType typ'
          return $ f inst
        case catMaybes matchingInstances of
          [] -> do
            logVerbose 25 "No matching instance"
            return Nothing
          matchingInstance:_ -> do
            logMeta 25 "Matching instance" matchingInstance
            logMeta 25 "Matching instance typ" typ'
            let sol = close (error "trySolveConstraint not closed") $ lams vs matchingInstance
            solve m sol
            return $ Just sol
      _ -> do
        logMeta 25 "Malformed" typ'
        throwLocated "Malformed constraint" -- TODO error message

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
solveDefConstraints (DataDefinition (DataDef ps constrs) rep) = do
  vs <- forTeleWithPrefixM ps $ \h p s vs -> do
    let t = instantiateTele pure vs s
    forall h p t

  constrs' <- withVars vs $ forM constrs $ \(ConstrDef c s) -> do
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
  logShow 35 "mergeConstraintVars" vars
  _ <- foldlM go mempty vars
  vars' <- filterMSet isUnsolved vars
  logShow 35 "mergeConstraintVars result" vars'
  return vars'
  where
    go varTypes m@MetaVar { metaPlicitness = Constraint } = do
      let arity = metaArity m
      msol <- solution m
      case msol of
        Just _ -> return varTypes
        Nothing -> do
          typ <- zonk $ open $ metaType m
          let ctyp = close id typ
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
    solveVar m m' = do
      (vs, _) <- instantiatedMetaType m'
      solve m'
        $ close (error "mergeConstraintVars not closed")
        $ lams vs
        $ Meta m
        $ (\v -> (varData v, pure v)) <$> vs

whnf :: CoreM -> Elaborate CoreM
whnf e = Normalise.whnf' Normalise.Args
  { Normalise.expandTypeReps = False
  , Normalise.handleMetaVar = trySolveMetaVar
  }
  e
  mempty

whnfExpandingTypeReps :: CoreM -> Elaborate CoreM
whnfExpandingTypeReps e = Normalise.whnf' Normalise.Args
  { Normalise.expandTypeReps = True
  , Normalise.handleMetaVar = trySolveMetaVar
  }
  e
  mempty
