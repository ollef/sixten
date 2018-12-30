{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Elaboration.Generalise where

import Protolude hiding (TypeError)

import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.Vector(Vector)

import Analysis.Simplify
import qualified Builtin.Names as Builtin
import Effect
import Elaboration.Constraint
import Elaboration.MetaVar
import Elaboration.MetaVar.Zonk
import Elaboration.Monad
import Syntax
import Syntax.Core
import TypedFreeVar
import Util
import Util.TopoSort

data GeneraliseDefsMode
  = GeneraliseType
  | GeneraliseAll
  deriving (Eq, Show)

generaliseDefs
  :: (MetaVar -> Bool)
  -> GeneraliseDefsMode
  -> Vector
    ( FreeV
    , GName
    , SourceLoc
    , Definition (Expr MetaVar) FreeV
    )
  -> Elaborate
    ( Vector
      ( FreeV
      , GName
      , SourceLoc
      , Definition (Expr MetaVar) FreeV
      )
    , FreeV -> FreeV
    )
generaliseDefs mpred mode defs = do
  defs' <- solveRecursiveDefConstraints defs
  metas <- collectMetas mpred mode defs'
  metas' <- mergeConstraintVars metas
  varMap <- generaliseMetas metas'
  logShow "tc.gen" "generaliseDefs varMap" varMap
  defs'' <- replaceMetas varMap defs'
  logShow "tc.gen" "generaliseDefs vars" (toHashSet $ HashMap.elems varMap)
  let defDeps = collectDefDeps (toHashSet $ HashMap.elems varMap) defs''
  replaceDefs defDeps

collectMetas
  :: (MetaVar -> Bool)
  -> GeneraliseDefsMode
  -> Vector
    ( FreeV
    , GName
    , SourceLoc
    , Definition (Expr MetaVar) FreeV
    )
  -> Elaborate (HashSet MetaVar)
collectMetas mpred mode defs = do
  -- After type-checking we may actually be in a situation where a dependency
  -- we thought existed doesn't actually exist because of class instances being
  -- resolved (unresolved class instances are assumed to depend on all
  -- instances), so we can't be sure that we have a single cycle. Therefore we
  -- separately compute dependencies for each definition.
  let isLocalConstraint m@MetaVar { metaPlicitness = Constraint }
        | mpred m = isUnsolved m
      isLocalConstraint _ = return False

  defVars <- case mode of
    GeneraliseType -> return mempty
    GeneraliseAll -> forM defs $ \(_, _, _, def) ->
      filterMSet isLocalConstraint =<< definitionMetaVars def

  typeVars <- forM defs $ \(v, _, _, _) -> do
    metas <- metaVars $ varType v
    logMeta "tc.gen" "varType" $ zonk $ varType v
    logShow "tc.gen" "collectMetas" metas
    filtered <- filterMSet (\m -> if not (mpred m) then return False else isUnsolved m) metas
    logShow "tc.gen" "collectMetas filtered" filtered
    return filtered

  return $ fold $ defVars <> typeVars

generaliseMetas
  :: HashSet MetaVar
  -> Elaborate (HashMap MetaVar FreeV)
generaliseMetas metas = do
  logShow "tc.gen" "generaliseMetas metas" metas
  instMetas <- forM (toList metas) $ \m -> do
    (instVs, instTyp) <- instantiatedMetaType m
    deps <- metaVars instTyp
    return (m, (instVs, instTyp, deps))

  let sortedMetas = acyclic <$> topoSortWith fst (thd3 . snd) instMetas
  logShow "tc.gen" "generaliseMetas sorted" sortedMetas

  flip execStateT mempty $ forM_ sortedMetas $ \(m, (instVs, instTyp, _deps)) -> do
    sub <- get
    let go m' es = do
          msol <- solution m'
          case msol of
            Nothing -> return $ case HashMap.lookup m' sub of
              Nothing -> Meta m' es
              Just v -> pure v
            Just e -> bindMetas' go $ betaApps (open e) es
    instTyp' <- bindMetas' go instTyp
    let localDeps = toHashSet instTyp' `HashSet.intersection` toHashSet instVs
    when (HashSet.null localDeps) $ do
      v <- forall (metaHint m) (metaPlicitness m) instTyp'
      modify $ HashMap.insert m v
      return ()
  where
    acyclic (AcyclicSCC a) = a
    acyclic (CyclicSCC _) = panic "generaliseMetas"

replaceMetas
  :: HashMap MetaVar FreeV
  -> Vector
    ( FreeV
    , GName
    , SourceLoc
    , Definition (Expr MetaVar) FreeV
    )
  -> Elaborate
    ( Vector
      ( FreeV
      , GName
      , SourceLoc
      , Definition (Expr MetaVar) FreeV
      , CoreM
      )
    )
replaceMetas varMap defs = forM defs $ \(v, name, loc, d) -> do
  logShow "tc.gen" "replaceMetas varMap" varMap
  logDefMeta "tc.gen" "replaceMetas def" $ zonkDef d
  d' <- bindDefMetas' go d
  t' <- bindMetas' go $ varType v
  logDefMeta "tc.gen" "replaceMetas def result" $ zonkDef d'
  return (v, name, loc, d', t')
  where
    go m es = do
      msol <- solution m
      case msol of
        Nothing -> case HashMap.lookup m varMap of
          Nothing -> do
            let Just typ = typeApps (open $ metaType m) es
            logCategory "tc.gen" $ "replaceMetas unsolved " <> show m
            typ' <- bindMetas' go typ
            reportUnresolvedMetaError typ'
            solve m $ Closed $ Builtin.Fail $ open $ metaType m
            -- TODO use actual error in expression when strings are faster
            return $ Builtin.Fail typ'
          Just v -> return $ pure v
        Just e -> bindMetas' go $ betaApps (open e) es
      where
        varKind = case metaPlicitness m of
          Constraint -> "constraint"
          Implicit -> "meta-variable"
          Explicit -> "meta-variable"
        reportUnresolvedMetaError typ = do
          printedTyp <- prettyMeta typ
          report $ TypeError ("Unresolved " <> varKind) (metaSourceLoc m)
            $ "A " <> varKind <> " of type " <> red printedTyp <> " could not be resolved."

collectDefDeps
  :: HashSet FreeV
  -> Vector
    ( FreeV
    , GName
    , SourceLoc
    , Definition (Expr MetaVar) FreeV
    , CoreM
    )
  -> Vector
    ( FreeV
    , ( GName
      , SourceLoc
      , Definition (Expr MetaVar) FreeV
      , CoreM
      , [FreeV]
      )
    )
collectDefDeps vars defs = do
  let allDeps = flip fmap defs $ \(v, name, loc, def, typ) -> do
        let d = toHashSet def
            t = toHashSet typ
        (v, (name, loc, def, typ, d <> t))
      sat
        = fmap acyclic
        . topoSortWith identity (toHashSet . varType)
        . HashSet.intersection vars
        . saturate (\v -> fold ((\(_, _, _, _, deps) -> deps) <$> hashedLookup allDeps v) <> toHashSet (varType v))
  fmap (\(name, loc, def, typ, deps) -> (name, loc, def, typ, sat deps)) <$> allDeps
  where
    acyclic (AcyclicSCC a) = a
    acyclic (CyclicSCC _) = panic "collectDefDeps"

replaceDefs
  :: Vector
    ( FreeV
    , ( GName
      , SourceLoc
      , Definition (Expr MetaVar) FreeV
      , CoreM
      , [FreeV]
      )
    )
  -> Elaborate
    ( Vector
      ( FreeV
      , GName
      , SourceLoc
      , Definition (Expr MetaVar) FreeV
      )
    , FreeV -> FreeV
    )
replaceDefs defs = do
  let appSubMap
        = toHashMap
        $ (\(v, (_, _, _, _, vs)) -> (v, apps (pure v) ((\v' -> (implicitise $ varData v', pure v')) <$> vs)))
        <$> defs
      appSub v = HashMap.lookupDefault (pure v) v appSubMap

  subbedDefs <- forM defs $ \(oldVar, (name, loc, def, typ, vs)) -> do
    logShow "tc.gen" "replaceDefs vs" (varId <$> vs)
    logDefMeta "tc.gen" "replaceDefs def" $ zonkDef def
    logMeta "tc.gen" "replaceDefs type" $ zonk typ
    let subbedDef = def >>>= appSub
        subbedType = typ >>= appSub
    (def', typ') <- abstractDefImplicits vs subbedDef subbedType
    logDefMeta "tc.gen" "replaceDefs subbedDef" $ zonkDef subbedDef
    logMeta "tc.gen" "replaceDefs subbedType" $ zonk subbedType
    newVar <- forall (varHint oldVar) (varData oldVar) typ'
    return (oldVar, newVar, name, loc, def')

  let renameMap
        = toHashMap
        $ (\(oldVar, newVar, _, _, _) -> (oldVar, newVar)) <$> subbedDefs
      rename v = HashMap.lookupDefault v v renameMap

      renamedDefs
        = (\(_, newVar, name, loc, def) -> (newVar { varType = rename <$> varType newVar }, name, loc, rename <$> def))
        <$> subbedDefs

  return (renamedDefs, rename)

abstractDefImplicits
  :: Foldable t
  => t FreeV
  -> Definition (Expr MetaVar) FreeV
  -> CoreM
  -> Elaborate (Definition (Expr MetaVar) FreeV, CoreM)
abstractDefImplicits vs (ConstantDefinition a e) t = do
  let ge = abstractImplicits vs lam e
      gt = abstractImplicits vs pi_ t
  return (ConstantDefinition a ge, gt)
abstractDefImplicits vs (DataDefinition (DataDef ps cs) rep) typ = do
  vs' <- forTeleWithPrefixM ps $ \h p s vs' -> do
    let t = instantiateTele pure vs' s
    forall h p t

  let cs' = [ConstrDef c $ instantiateTele pure vs' s | ConstrDef c s <- cs]

  let grep = abstractImplicits vs lam rep
      gtyp = abstractImplicits vs pi_ typ
  return (DataDefinition (dataDef (implicitiseVar <$> toVector vs <|> vs') cs') grep, gtyp)
  where
    implicitiseVar v = v { varData = implicitise $ varData v }

abstractImplicits
  :: Foldable t
  => t FreeV
  -> (FreeV -> CoreM -> CoreM)
  -> CoreM
  -> CoreM
abstractImplicits vs c b = foldr (\v -> c (v { varData = implicitise $ varData v })) b vs
