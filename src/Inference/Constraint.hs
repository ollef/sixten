{-# LANGUAGE FlexibleContexts, OverloadedStrings, ViewPatterns #-}
module Inference.Constraint where

import Control.Monad.Except
import Data.Bifunctor
import Data.Foldable
import Data.HashSet(HashSet)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Vector(Vector)
import Data.Void

import Analysis.Simplify
import Inference.MetaVar
import Inference.MetaVar.Zonk
import Inference.Monad
import qualified Inference.Normalise as Normalise
import Inference.Subtype
import MonadContext
import Syntax
import Syntax.Core
import TypedFreeVar
import Util
import VIX

elabMetaVar
  :: MetaVar
  -> Infer (Maybe (Closed (Expr MetaVar)))
elabMetaVar m = do
  msol <- solution m
  case (msol, metaPlicitness m) of
    (Nothing, Constraint) -> elabUnsolvedConstraint m
    (Nothing, _) -> return Nothing
    (Just e, _) -> return $ Just e

elabUnsolvedConstraint
  :: MetaVar
  -> Infer (Maybe (Closed (Expr MetaVar)))
elabUnsolvedConstraint m = inUpdatedContext (const mempty) $ do
  logShow 25 "elabUnsolvedConstraint" $ metaId m
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
            let sol = close (error "elabUnsolvedConstraint not closed") $ lams vs matchingInstance
            solve m sol
            return $ Just sol
      _ -> do
        logMeta 25 "Malformed" typ'
        throwLocated "Malformed constraint" -- TODO error message

elabExpr
  :: CoreM
  -> Infer CoreM
elabExpr = bindMetas $ \m es -> do
  sol <- elabMetaVar m
  case sol of
    Nothing -> Meta m <$> traverse (traverse elabExpr) es
    Just e -> elabExpr $ betaApps (open e) es

elabDef
  :: Definition (Expr MetaVar) FreeV
  -> Infer (Definition (Expr MetaVar) FreeV)
elabDef (ConstantDefinition a e)
  = ConstantDefinition a <$> elabExpr e
elabDef (DataDefinition (DataDef ps constrs) rep) = do
  vs <- forTeleWithPrefixM ps $ \h p s vs -> do
    let t = instantiateTele pure vs s
    forall h p t

  constrs' <- withVars vs $ forM constrs $ \(ConstrDef c s) -> do
    let e = instantiateTele pure vs s
    e' <- elabExpr e
    return $ ConstrDef c e'

  rep' <- elabExpr rep
  return $ DataDefinition (dataDef vs constrs') rep'

elabRecursiveDefs
  :: Vector (FreeV, name, loc, Definition (Expr MetaVar) FreeV)
  -> Infer (Vector (FreeV, name, loc, Definition (Expr MetaVar) FreeV))
elabRecursiveDefs defs = forM defs $ \(v, name, loc, def) -> do
  def' <- elabDef def
  _typ' <- elabExpr $ varType v
  return (v, name, loc, def')

mergeConstraintVars
  :: HashSet MetaVar
  -> Infer (HashSet MetaVar) -- ^ The metavars that are still unsolved
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

whnf :: CoreM -> Infer CoreM
whnf e = Normalise.whnf' Normalise.Args
  { Normalise.expandTypeReps = False
  , Normalise.handleMetaVar = elabMetaVar
  }
  e
  mempty

whnfExpandingTypeReps :: CoreM -> Infer CoreM
whnfExpandingTypeReps e = Normalise.whnf' Normalise.Args
  { Normalise.expandTypeReps = True
  , Normalise.handleMetaVar = elabMetaVar
  }
  e
  mempty
