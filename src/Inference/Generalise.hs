{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Inference.Generalise where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Data.Foldable as Foldable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.Vector(Vector)

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
    , QName
    , SourceLoc
    , Definition (Expr MetaVar) FreeV
    )
  -> Infer
    ( Vector
      ( FreeV
      , QName
      , SourceLoc
      , Definition (Expr MetaVar) FreeV
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
    , QName
    , SourceLoc
    , Definition (Expr MetaVar) FreeV
    )
  -> Infer (HashSet MetaVar)
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
    logShow 30 "collectMetas" metas
    filtered <- filterMSet (\m -> if not (mpred m) then return False else isUnsolved m) metas
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
    acyclic (CyclicSCC _) = error "generaliseMetas"

replaceMetas
  :: HashMap MetaVar FreeV
  -> Vector
    ( FreeV
    , QName
    , SourceLoc
    , Definition (Expr MetaVar) FreeV
    )
  -> Infer
    ( Vector
      ( FreeV
      , QName
      , SourceLoc
      , Definition (Expr MetaVar) FreeV
      , CoreM
      )
    )
replaceMetas varMap defs = forM defs $ \(v, name, loc, d) -> do
  logShow 30 "replaceMetas varMap" varMap
  logDefMeta 30 "replaceMetas def" d
  d' <- bindDefMetas' go d
  t' <- bindMetas' go $ varType v
  logDefMeta 30 "replaceMetas def result" d'
  return (v, name, loc, d', t')
  where
    go m es = do
      msol <- solution m
      case msol of
        Nothing -> case HashMap.lookup m varMap of
          Nothing -> do
            unsolved <- isUnsolved m
            if unsolved then do
              let Just typ = typeApps (open $ metaType m) es
              typ' <- bindMetas' go typ
              reportUnresolvedMetaError typ'
              -- TODO use actual error in expression when strings are faster
              return $ Builtin.Fail typ'
            else
              return $ Meta m es
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
    , QName
    , SourceLoc
    , Definition (Expr MetaVar) FreeV
    , CoreM
    )
  -> Vector
    ( FreeV
    , ( QName
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
        . topoSortWith id (toHashSet . varType)
        . HashSet.intersection vars
        . saturate (\v -> fold (fmap (\(_, _, _, _, deps) -> deps) $ hashedLookup allDeps v) <> toHashSet (varType v))
  fmap (\(name, loc, def, typ, deps) -> (name, loc, def, typ, sat deps)) <$> allDeps
  where
    acyclic (AcyclicSCC a) = a
    acyclic (CyclicSCC _) = error "collectDefDeps"

replaceDefs
  :: Vector
    ( FreeV
    , ( QName
      , SourceLoc
      , Definition (Expr MetaVar) FreeV
      , CoreM
      , [FreeV]
      )
    )
  -> Infer
    ( Vector
      ( FreeV
      , QName
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
    logShow 30 "replaceDefs vs" (varId <$> vs)
    logDefMeta 30 "replaceDefs def" def
    logMeta 30 "replaceDefs type" typ
    let subbedDef = def >>>= appSub
        subbedType = typ >>= appSub
    (def', typ') <- abstractDefImplicits vs subbedDef subbedType
    logDefMeta 30 "replaceDefs subbedDef" subbedDef
    logMeta 30 "replaceDefs subbedType" subbedType
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
  -> Infer (Definition (Expr MetaVar) FreeV, CoreM)
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
