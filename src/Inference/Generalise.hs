{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Inference.Generalise where

import Control.Monad.Except
import Control.Monad.State
import Data.Foldable as Foldable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.Monoid
import Data.Vector(Vector)
import Data.Void

import Analysis.Simplify
import qualified Builtin.Names as Builtin
import Inference.Constraint
import Inference.MetaVar
import Inference.MetaVar.Zonk
import Inference.Monad
import Syntax
import Syntax.Core
import TypedFreeVar
import Util
import Util.TopoSort
import VIX

data GeneraliseDefsMode
  = GeneraliseType
  | GeneraliseAll
  deriving (Eq, Show)

generaliseDefs
  :: (MetaVar -> Bool)
  -> GeneraliseDefsMode
  -> Vector
    ( FreeV
    , Definition (Expr MetaVar) FreeV
    , CoreM
    )
  -> Infer
    ( Vector
      ( FreeV
      , Definition (Expr MetaVar) FreeV
      , CoreM
      )
    , FreeV -> FreeV
    )
generaliseDefs mpred mode defs = do
  defs' <- elabRecursiveDefs defs
  metas <- collectMetas mpred mode defs'
  metas' <- mergeConstraintVars metas
  varMap <- generaliseMetas metas'
  logShow 30 "generaliseDefs varMap" varMap
  defs'' <- replaceMetas varMap defs'
  logShow 30 "generaliseDefs vars" (toHashSet $ HashMap.elems varMap)
  let defDeps = collectDefDeps (toHashSet $ HashMap.elems varMap) defs''
  replaceDefs defDeps

collectMetas
  :: (MetaVar -> Bool)
  -> GeneraliseDefsMode
  -> Vector
    ( FreeV
    , Definition (Expr MetaVar) FreeV
    , CoreM
    )
  -> Infer (HashSet MetaVar)
collectMetas mpred mode defs = do
  -- After type-checking we may actually be in a situation where a dependency
  -- we thought existed doesn't actually exist because of class instances being
  -- resolved (unresolved class instances are assumed to depend on all
  -- instances), so we can't be sure that we have a single cycle. Therefore we
  -- separately compute dependencies for each definition.
  let isLocalConstraint m@MetaVar { metaPlicitness = Constraint }
        | mpred m = isLocalMeta m
      isLocalConstraint _ = return False

  defVars <- case mode of
    GeneraliseType -> return mempty
    GeneraliseAll -> forM defs $ \(_, def, _) ->
      filterMSet isLocalConstraint =<< definitionMetaVars def

  typeVars <- forM defs $ \(_, _, typ) -> do
    metas <- metaVars typ
    logShow 30 "collectMetas" metas
    filtered <- filterMSet (\m -> if not (mpred m) then return False else isLocalMeta m) metas
    logShow 30 "collectMetas filtered" filtered
    return filtered

  return $ fold $ defVars <> typeVars

generaliseMetas
  :: HashSet MetaVar
  -> Infer (HashMap MetaVar FreeV)
generaliseMetas metas = do
  logShow 30 "generaliseMetas metas" metas
  instMetas <- forM (toList metas) $ \m -> do
    (instVs, instTyp) <- instantiatedMetaType m
    deps <- metaVars instTyp
    return (m, (instVs, instTyp, deps))

  let sortedMetas = acyclic <$> topoSortWith fst (thd3 . snd) instMetas
  logShow 30 "generaliseMetas sorted" sortedMetas

  flip execStateT mempty $ forM_ sortedMetas $ \(m, (instVs, instTyp, _deps)) -> do
    sub <- get
    let go m' es = do
          sol <- solution m'
          case sol of
            Left _ -> return $ case HashMap.lookup m' sub of
              Nothing -> Meta m' es
              Just v -> pure v
            Right e -> bindMetas' go $ betaApps (vacuous e) es
    instTyp' <- bindMetas' go instTyp
    let localDeps = toHashSet instTyp' `HashSet.intersection` toHashSet instVs
    when (HashSet.null localDeps) $ do
      v <- forall (metaHint m) (metaPlicitness m) instTyp'
      modify $ HashMap.insert m v
      return ()
  where
    acyclic (AcyclicSCC a) = a
    acyclic (CyclicSCC _) = error "generaliseMetas"

replaceMetas
  :: HashMap MetaVar FreeV
  -> Vector
    ( FreeV
    , Definition (Expr MetaVar) FreeV
    , CoreM
    )
  -> Infer
    ( Vector
      ( FreeV
      , Definition (Expr MetaVar) FreeV
      , CoreM
      )
    )
replaceMetas varMap defs = forM defs $ \(v, d, t) -> do
  logShow 30 "replaceMetas varMap" varMap
  logDefMeta 30 "replaceMetas def" d
  (d', t') <- bindDefMetas' go d t
  logDefMeta 30 "replaceMetas def result" d'
  return (v, d', t')
  where
    go m es = do
      sol <- solution m
      case sol of
        Left _ -> case HashMap.lookup m varMap of
          Nothing -> do
            local <- isLocalMeta m
            if local then do
              let Just typ = typeApps (vacuous $ metaType m) es
              typ' <- bindMetas' go typ
              reportUnresolvedMetaError typ'
              -- TODO use actual error in expression when strings are faster
              return $ Builtin.Fail typ'
            else
              return $ Meta m es
          Just v -> return $ pure v
        Right e -> bindMetas' go $ betaApps (vacuous e) es
      where
        varKind = case metaPlicitness m of
          Constraint -> "constraint"
          Implicit -> "meta-variable"
          Explicit -> "meta-variable"
        reportUnresolvedMetaError typ = do
          printedTyp <- prettyMeta typ
          report $ TypeError ("Unresolved " <> varKind) (metaSourceLoc m)
            $ "A " <> varKind <> " of type " <> red printedTyp <> " could not be resolved."

isLocalMeta :: MetaVar -> Infer Bool
isLocalMeta m = do
  l <- level
  either (>= l) (const False) <$> solution m

collectDefDeps
  :: HashSet FreeV
  -> Vector
    ( FreeV
    , Definition (Expr MetaVar) FreeV
    , CoreM
    )
  -> Vector
    ( FreeV
    , ( Definition (Expr MetaVar) FreeV
      , CoreM
      , [FreeV]
      )
    )
collectDefDeps vars defs = do
  let allDeps = flip fmap defs $ \(v, def, typ) -> do
        let d = toHashSet def
            t = toHashSet typ
        (v, (def, typ, d <> t))
      sat
        = fmap acyclic
        . topoSortWith id (toHashSet . varType)
        . HashSet.intersection vars
        . saturate (\v -> fold (fmap thd3 $ hashedLookup allDeps v) <> toHashSet (varType v))
  fmap (\(def, typ, deps) -> (def, typ, sat deps)) <$> allDeps
  where
    acyclic (AcyclicSCC a) = a
    acyclic (CyclicSCC _) = error "collectDefDeps"

replaceDefs
  :: Vector
    ( FreeV
    , ( Definition (Expr MetaVar) FreeV
      , CoreM
      , [FreeV]
      )
    )
  -> Infer
    ( Vector
      ( FreeV
      , Definition (Expr MetaVar) FreeV
      , CoreM
      )
    , FreeV -> FreeV
    )
replaceDefs defs = do
  let appSubMap
        = toHashMap
        $ (\(v, (_, _, vs)) -> (v, apps (pure v) ((\v' -> (implicitise $ varData v', pure v')) <$> vs)))
        <$> defs
      appSub v = HashMap.lookupDefault (pure v) v appSubMap

  subbedDefs <- forM defs $ \(oldVar, (def, typ, vs)) -> do
    logShow 30 "replaceDefs vs" (varId <$> vs)
    logDefMeta 30 "replaceDefs def" def
    logMeta 30 "replaceDefs type" typ
    let subbedDef = def >>>= appSub
        subbedType = typ >>= appSub
        (def', typ') = abstractDefImplicits vs subbedDef subbedType
    logDefMeta 30 "replaceDefs subbedDef" subbedDef
    logMeta 30 "replaceDefs subbedType" subbedType
    newVar <- forall (varHint oldVar) (varData oldVar) typ'
    return (oldVar, newVar, def')

  let renameMap
        = toHashMap
        $ (\(oldVar, newVar, _) -> (oldVar, newVar)) <$> subbedDefs
      rename v = HashMap.lookupDefault v v renameMap

      renamedDefs
        = (\(_, newVar, def) -> (newVar, rename <$> def, rename <$> varType newVar))
        <$> subbedDefs

  return (renamedDefs, rename)

abstractDefImplicits
  :: Foldable t
  => t FreeV
  -> Definition (Expr MetaVar) FreeV
  -> CoreM
  -> (Definition (Expr MetaVar) FreeV, CoreM)
abstractDefImplicits vs (Definition a i e) t = do
  let ge = abstractImplicits vs lam e
      gt = abstractImplicits vs pi_ t
  (Definition a i ge, gt)
abstractDefImplicits vs (DataDefinition (DataDef cs) rep) typ = do
  let cs' = map (fmap $ toScope . splat f g) cs
  -- Abstract vs on top of typ
  let grep = abstractImplicits vs lam rep
      gtyp = abstractImplicits vs pi_ typ
  (DataDefinition (DataDef cs') grep, gtyp)
  where
    varIndex = hashedElemIndex $ toVector vs
    f v = pure $ maybe (F v) (B . TeleVar) (varIndex v)
    g = pure . B . (+ TeleVar (length vs))

abstractImplicits
  :: Foldable t
  => t FreeV
  -> (FreeV -> CoreM -> CoreM)
  -> CoreM
  -> CoreM
abstractImplicits vs c b = foldr (\v -> c (v { varData = implicitise $ varData v })) b vs
