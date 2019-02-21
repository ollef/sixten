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
import Effect.Context as Context
import Elaboration.Constraint
import Elaboration.MetaVar
import Elaboration.MetaVar.Zonk
import Elaboration.Monad
import Syntax
import Syntax.Core
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
    ( Var
    , GName
    , SourceLoc
    , Definition (Expr MetaVar) Var
    )
  -> Elaborate
    ( Vector
      ( Var
      , GName
      , SourceLoc
      , Definition (Expr MetaVar) Var
      , CoreM
      )
    )
generaliseDefs mpred mode defs = do
  defs' <- solveRecursiveDefConstraints defs
  metas <- collectMetas mpred mode defs'
  metas' <- mergeConstraintVars metas
  varMap <- generaliseMetas metas'
  logShow "tc.gen" "generaliseDefs varMap" varMap
  let
    sortedVars
      = topoSortWith fst (foldMap toHashSet . snd) $ HashMap.elems varMap
  logShow "tc.gen" "generaliseDefs vars" sortedVars
  Context.extends (acyclic <$> sortedVars) $ do
    defs'' <- replaceMetas varMap defs'
    let
      defDeps = collectDefDeps (toHashMap $ HashMap.elems varMap) defs''
    replaceDefs defDeps
  where
    acyclic (CyclicSCC _) = panic "generaliseDefs cyclic vars"
    acyclic (AcyclicSCC x) = x

collectMetas
  :: (MetaVar -> Bool)
  -> GeneraliseDefsMode
  -> Vector
    ( Var
    , GName
    , SourceLoc
    , Definition (Expr MetaVar) Var
    )
  -> Elaborate (HashSet MetaVar)
collectMetas mpred mode defs = do
  -- After type-checking we may actually be in a situation where a dependency
  -- we thought existed doesn't actually exist because of class instances being
  -- resolved (unresolved class instances are assumed to depend on all
  -- instances), so we can't be sure that we have a single cycle. Therefore we
  -- separately compute dependencies for each definition.
  let
    isLocalConstraint m@MetaVar { metaPlicitness = Constraint }
      | mpred m = isUnsolved m
    isLocalConstraint _ = return False

  defVars <- case mode of
    GeneraliseType -> return mempty
    GeneraliseAll -> forM defs $ \(_, _, _, def) ->
      filterMSet isLocalConstraint =<< definitionMetaVars def

  typeVars <- forM defs $ \(v, _, _, _) -> do
    varType <- Context.lookupType v
    metas <- metaVars varType
    logMeta "tc.gen" "varType" $ zonk varType
    logShow "tc.gen" "collectMetas" metas
    filtered <- filterMSet (\m -> if not (mpred m) then return False else isUnsolved m) metas
    logShow "tc.gen" "collectMetas filtered" filtered
    return filtered

  return $ fold $ defVars <> typeVars

generaliseMetas
  :: HashSet MetaVar
  -> Elaborate (HashMap MetaVar (Var, Binding CoreM))
generaliseMetas metas = do
  logShow "tc.gen" "generaliseMetas metas" metas
  instMetas <- forM (toList metas) $ \m ->
    withInstantiatedMetaType m $ \instVs instTyp -> do
      deps <- metaVars instTyp
      return (m, (instVs, instTyp, deps))

  let
    sortedMetas = acyclic <$> topoSortWith fst (thd3 . snd) instMetas
  logShow "tc.gen" "generaliseMetas sorted" sortedMetas

  flip execStateT mempty $ forM_ sortedMetas $ \(m, (instVs, instTyp, _deps)) -> do
    sub <- get
    let
      go m' es = do
        msol <- solution m'
        case msol of
          Nothing -> return $ case HashMap.lookup m' sub of
            Nothing -> Meta m' es
            Just (v, _) -> pure v
          Just e -> bindMetas' go $ betaApps (open e) es
    instTyp' <- bindMetas' go instTyp
    let
      localDeps = toHashSet instTyp' `HashSet.intersection` toHashSet instVs
    when (HashSet.null localDeps) $ do
      v <- freeVar
      modify
        $ HashMap.insert m
          (v, binding (metaHint m) (metaPlicitness m) instTyp')
  where
    acyclic (AcyclicSCC a) = a
    acyclic (CyclicSCC _) = panic "generaliseMetas"

replaceMetas
  :: HashMap MetaVar (Var, Binding CoreM)
  -> Vector
    ( Var
    , GName
    , SourceLoc
    , Definition (Expr MetaVar) Var
    )
  -> Elaborate
    ( Vector
      ( Var
      , GName
      , SourceLoc
      , Definition (Expr MetaVar) Var
      , CoreM
      )
    )
replaceMetas varMap defs = forM defs $ \(v, name, loc, d) -> do
  logShow "tc.gen" "replaceMetas varMap" varMap
  logDefMeta "tc.gen" "replaceMetas def" $ zonkDef d
  t <- Context.lookupType v
  d' <- bindDefMetas' go d
  t' <- bindMetas' go t
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
          Just (v, _) -> return $ pure v
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
  :: HashMap Var (Binding CoreM)
  -> Vector
    ( Var
    , GName
    , SourceLoc
    , Definition (Expr MetaVar) Var
    , CoreM
    )
  -> Vector
    ( Var
    , ( GName
      , SourceLoc
      , Definition (Expr MetaVar) Var
      , CoreM
      , [Var]
      )
    )
collectDefDeps vars defs = do
  let
    allDeps = flip fmap defs $ \(v, name, loc, def, typ) -> do
      let
        d = toHashSet def
        t = toHashSet typ
      (v, (name, loc, def, typ, d <> t))
    sat
      = fmap acyclic
      . topoSortWith identity (toHashSet . Context._type . (vars HashMap.!))
      . HashSet.intersection (HashSet.fromMap $ void vars)
      . saturate (\v -> fold $ (\(_, _, _, _, deps) -> deps) <$> hashedLookup allDeps v)
  fmap (\(name, loc, def, typ, deps) -> (name, loc, def, typ, sat deps)) <$> allDeps
  where
    acyclic (AcyclicSCC a) = a
    acyclic (CyclicSCC _) = panic "collectDefDeps"

replaceDefs
  :: Vector
    ( Var
    , ( GName
      , SourceLoc
      , Definition (Expr MetaVar) Var
      , CoreM
      , [Var]
      )
    )
  -> Elaborate
    ( Vector
      ( Var
      , GName
      , SourceLoc
      , Definition (Expr MetaVar) Var
      , CoreM
      )
    )
replaceDefs defs = do
  ctx <- getContext
  let
    appSubMap
      = toHashMap
      $ (\(v, (_, _, _, _, vs)) -> (v, apps (pure v) ((\v' -> (implicitise $ lookupPlicitness v' ctx, pure v')) <$> vs)))
      <$> defs
    appSub v = HashMap.lookupDefault (pure v) v appSubMap

  forM defs $ \(var, (name, loc, def, typ, vs)) -> do
    logShow "tc.gen" "replaceDefs vs" vs
    logDefMeta "tc.gen" "replaceDefs def" $ zonkDef def
    logMeta "tc.gen" "replaceDefs type" $ zonk typ
    let
      subbedDef = def >>>= appSub
      subbedType = typ >>= appSub
    (def', typ') <- abstractDefImplicits vs subbedDef subbedType
    logDefMeta "tc.gen" "replaceDefs subbedDef" $ zonkDef subbedDef
    logMeta "tc.gen" "replaceDefs subbedType" $ zonk subbedType
    return (var, name, loc, def', typ')

abstractDefImplicits
  :: (Functor t, Foldable t)
  => t Var
  -> Definition (Expr MetaVar) Var
  -> CoreM
  -> Elaborate (Definition (Expr MetaVar) Var, CoreM)
abstractDefImplicits vs (ConstantDefinition a e) t = do
  ctx <- getContext
  let
    pvs = (\v -> (implicitise $ Context.lookupPlicitness v ctx, v)) <$> vs
  ge <- plicitLams pvs e
  gt <- plicitPis pvs t
  return (ConstantDefinition a ge, gt)
abstractDefImplicits vs (DataDefinition (DataDef ps cs) rep) typ =
  teleExtendContext ps $ \vs' -> do
    ctx <- getContext
    let
      cs' = [ConstrDef c $ instantiateTele pure vs' s | ConstrDef c s <- cs]
      pvs = (\v -> (implicitise $ Context.lookupPlicitness v ctx, v)) <$> vs
      pvs' = (\v -> (Context.lookupPlicitness v ctx, v)) <$> vs'

    grep <- plicitLams pvs rep
    gtyp <- plicitPis pvs typ
    dd <- plicitDataDef (toVector pvs <> pvs') cs'
    return (DataDefinition dd grep, gtyp)
