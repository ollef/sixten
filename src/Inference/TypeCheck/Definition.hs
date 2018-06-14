{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Inference.TypeCheck.Definition where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable as Foldable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.Monoid
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import {-# SOURCE #-} Inference.TypeCheck.Expr
import Analysis.Simplify
import qualified Builtin.Names as Builtin
import Inference.Constraint
import Inference.Cycle
import Inference.MetaVar
import Inference.MetaVar.Zonk
import Inference.Monad
import Inference.TypeCheck.Clause
import Inference.TypeCheck.Data
import Inference.Unify
import MonadContext
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete.Scoped as Concrete
import TypedFreeVar
import Util
import Util.TopoSort
import VIX

checkDefType
  :: Concrete.PatDefinition (Concrete.Clause Void Concrete.Expr FreeV)
  -> AbstractM
  -> Infer (Definition (Abstract.Expr MetaVar) FreeV, AbstractM)
checkDefType (Concrete.PatDefinition a i clauses) typ = do
  e' <- checkClauses clauses typ
  return (Definition a i e', typ)

checkTopLevelDefType
  :: FreeV
  -> Concrete.TopLevelPatDefinition Concrete.Expr FreeV
  -> SourceLoc
  -> AbstractM
  -> Infer (Definition (Abstract.Expr MetaVar) FreeV, AbstractM)
checkTopLevelDefType v def loc typ = located loc $ case def of
  Concrete.TopLevelPatDefinition def' -> checkDefType def' typ
  Concrete.TopLevelPatDataDefinition d -> checkDataType v d typ
  -- Should be removed by Declassify:
  Concrete.TopLevelPatClassDefinition _ -> error "checkTopLevelDefType class"
  Concrete.TopLevelPatInstanceDefinition _ -> error "checkTopLevelDefType instance"

abstractDefImplicits
  :: Foldable t
  => t FreeV
  -> Definition (Abstract.Expr MetaVar) FreeV
  -> AbstractM
  -> (Definition (Abstract.Expr MetaVar) FreeV, AbstractM)
abstractDefImplicits vs (Definition a i e) t = do
  let ge = abstractImplicits vs Abstract.Lam e
      gt = abstractImplicits vs Abstract.Pi t
  (Definition a i ge, gt)
abstractDefImplicits vs (DataDefinition (DataDef cs) rep) typ = do
  let cs' = map (fmap $ toScope . splat f g) cs
  -- Abstract vs on top of typ
  let grep = abstractImplicits vs Abstract.Lam rep
      gtyp = abstractImplicits vs Abstract.Pi typ
  (DataDefinition (DataDef cs') grep, gtyp)
  where
    varIndex = hashedElemIndex $ toVector vs
    f v = pure $ maybe (F v) (B . TeleVar) (varIndex v)
    g = pure . B . (+ TeleVar (length vs))

abstractImplicits
  :: Foldable t
  => t FreeV
  -> (NameHint -> Plicitness -> AbstractM -> Scope () (Abstract.Expr MetaVar) FreeV -> AbstractM)
  -> AbstractM
  -> AbstractM
abstractImplicits vs c b = foldr
  (\v s -> c (varHint v) (implicitise $ varData v) (varType v) $ abstract1 v s)
  b
  vs

data GeneraliseDefsMode
  = GeneraliseType
  | GeneraliseAll
  deriving (Eq, Show)

generaliseDefs
  :: GeneraliseDefsMode
  -> Vector
    ( FreeV
    , Definition (Abstract.Expr MetaVar) FreeV
    , AbstractM
    )
  -> Infer
    ( Vector
      ( FreeV
      , Definition (Abstract.Expr MetaVar) FreeV
      , AbstractM
      )
    , FreeV -> FreeV
    )
generaliseDefs mode defs = do
  defs' <- elabRecursiveDefs defs
  metas <- collectMetas mode defs'
  metas' <- mergeConstraintVars metas
  varMap <- generaliseMetas metas'
  logShow 30 "generaliseDefs varMap" varMap
  defs'' <- replaceMetas varMap defs'
  logShow 30 "generaliseDefs vars" (toHashSet $ HashMap.elems varMap)
  let defDeps = collectDefDeps (toHashSet $ HashMap.elems varMap) defs''
  replaceDefs defDeps

collectMetas
  :: GeneraliseDefsMode
  -> Vector
    ( FreeV
    , Definition (Abstract.Expr MetaVar) FreeV
    , AbstractM
    )
  -> Infer (HashSet MetaVar)
collectMetas mode defs = do
  -- After type-checking we may actually be in a situation where a dependency
  -- we thought existed doesn't actually exist because of class instances being
  -- resolved (unresolved class instances are assumed to depend on all
  -- instances), so we can't be sure that we have a single cycle. Therefore we
  -- separately compute dependencies for each definition.
  let isLocalConstraint m@MetaVar { metaPlicitness = Constraint } = isLocalMeta m
      isLocalConstraint _ = return False

  -- TODO use special form of metaVars that doesn't count metavar dependencies?

  defVars <- case mode of
    GeneraliseType -> return mempty
    GeneraliseAll -> forM defs $ \(_, def, _) ->
      filterMSet isLocalConstraint =<< definitionMetaVars def

  typeVars <- forM defs $ \(_, _, typ) -> do
    metas <- metaVars typ
    logShow 30 "collectMetas" metas
    filtered <- filterMSet isLocalMeta metas
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
              Nothing -> Abstract.Meta m' es
              Just v -> pure v
            Right e -> bindMetas' go $ betaApps (vacuous e) es
    instTyp' <- bindMetas' go instTyp
    let localDeps = toHashSet instTyp' `HashSet.intersection` toHashSet instVs
    unless (HashSet.null localDeps) $ error "generaliseMetas local deps" -- TODO error message
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
    , Definition (Abstract.Expr MetaVar) FreeV
    , AbstractM
    )
  -> Infer
    ( Vector
      ( FreeV
      , Definition (Abstract.Expr MetaVar) FreeV
      , AbstractM
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
              let Just typ = Abstract.typeApps (vacuous $ metaType m) es
                  varKind = case metaPlicitness m of
                    Constraint -> "constraint"
                    Implicit -> "meta-variable"
                    Explicit -> "meta-variable"
              typ' <- bindMetas' go typ
              printedTyp <- prettyMeta typ'
              report $ TypeError ("Unresolved " <> varKind) (metaSourceLoc m)
                $ "A " <> varKind <> " of type " <> red printedTyp <> " could not be resolved."
              -- TODO use actual error in expression when strings are faster
              return $ Builtin.Fail typ'
            else
              return $ Abstract.Meta m es
          Just v -> return $ pure v
        Right e -> bindMetas' go $ betaApps (vacuous e) es

isLocalMeta :: MetaVar -> Infer Bool
isLocalMeta m = do
  l <- level
  either (>= l) (const False) <$> solution m

collectDefDeps
  :: HashSet FreeV
  -> Vector
    ( FreeV
    , Definition (Abstract.Expr MetaVar) FreeV
    , AbstractM
    )
  -> Vector
    ( FreeV
    , ( Definition (Abstract.Expr MetaVar) FreeV
      , AbstractM
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
    , ( Definition (Abstract.Expr MetaVar) FreeV
      , AbstractM
      , [FreeV]
      )
    )
  -> Infer
    ( Vector
      ( FreeV
      , Definition (Abstract.Expr MetaVar) FreeV
      , AbstractM
      )
    , FreeV -> FreeV
    )
replaceDefs defs = do
  let appSubMap
        = toHashMap
        $ (\(v, (_, _, vs)) -> (v, Abstract.apps (pure v) ((\v' -> (implicitise $ varData v', pure v')) <$> vs)))
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

checkRecursiveDefs
  :: Bool
  -> Vector
    ( FreeV
    , ( SourceLoc
      , Concrete.TopLevelPatDefinition Concrete.Expr FreeV
      , Maybe ConcreteM
      )
    )
  -> Infer
    (Vector
      ( FreeV
      , Definition (Abstract.Expr MetaVar) FreeV
      , AbstractM
      )
    )
checkRecursiveDefs forceGeneralisation defs = do
  let gen = forceGeneralisation || shouldGeneralise defs
      -- Prevent metavariables to recursively refer to the bindings in this
      -- binding group unless we know we're going to generalise
      withDefVars = if gen then withVars (fst <$> defs) else id
  withDefVars $ do
    -- Divide the definitions into ones with and without type signature.
    let (noSigDefs, sigDefs) = divide defs

    -- Assume that the specified type signatures are correct.
    sigDefs' <- forM sigDefs $ \(evar, (loc, def, typ)) -> do
      typ' <- checkPoly typ Builtin.Type
      unify [] (varType evar) typ'
      return (evar, (loc, def))

    -- The definitions without type signature are checked and generalised,
    -- assuming the type signatures of the others.
    noSigResult <- checkTopLevelDefs noSigDefs

    result <- if gen then do

      -- Generalise the definitions without signature
      (genNoSigResult, noSigSub) <- generaliseDefs GeneraliseAll noSigResult

      subbedSigDefs <- forM sigDefs' $ \(v, (loc, def)) -> do
        let def' = def >>>= pure . noSigSub
        return (v, (loc, def'))

      sigResult <- checkTopLevelDefs subbedSigDefs

      -- Generalise the definitions with signature
      if Vector.null sigResult then
          -- No need to generalise again if there are actually no definitions
          -- with signatures
          return genNoSigResult
        else do
          (genResult, _) <- generaliseDefs GeneraliseType $ genNoSigResult <> sigResult
          return genResult
    else do
      sigResult <- checkTopLevelDefs sigDefs'
      return $ noSigResult <> sigResult

    let locs = (\(_, (loc, _)) -> loc) <$> noSigDefs
          <|> (\(_, (loc, _)) -> loc) <$> sigDefs'

    unless (Vector.length locs == Vector.length result) $
      internalError $ "checkRecursiveDefs unmatched length" PP.<+> shower (Vector.length locs) PP.<+> shower (Vector.length result)

    let locResult = Vector.zip locs result

    detectTypeRepCycles locResult
    detectDefCycles locResult

    let permutation = Vector.zip (fst <$> defs) (fst <$> noSigDefs <|> fst <$> sigDefs)
    return $ unpermute permutation result
    where
      divide = bimap Vector.fromList Vector.fromList . foldMap go
        where
          go (v, (loc, def, Nothing)) = ([(v, (loc, def))], [])
          go (v, (loc, def, Just t)) = ([], [(v, (loc, def, t))])

checkTopLevelDefs
  :: Vector
    ( FreeV
    , ( SourceLoc
      , Concrete.TopLevelPatDefinition Concrete.Expr FreeV
      )
    )
  -> Infer
    (Vector
      ( FreeV
      , Definition (Abstract.Expr MetaVar) FreeV
      , AbstractM
      )
    )
checkTopLevelDefs defs = indentLog $ do
  -- forM_ defs $ \(var, (_, def)) ->
  --   logMeta 20 ("checkTopLevelDefs " ++ show (pretty $ fromNameHint "" id $ varHint var)) def

  checkedDefs <- forM defs $ \(var, (loc, def)) -> do
    (def', typ'') <- checkTopLevelDefType var def loc $ varType var
    return (var, def', typ'')

--   forM_ elabDefs $ \(var, def, typ) -> do
--     logMeta 20 ("checkTopLevelDefs res " ++ show (pretty $ fromNameHint "" id $ metaHint var)) def
--     logMeta 20 ("checkTopLevelDefs res t " ++ show (pretty $ fromNameHint "" id $ metaHint var)) typ

  return checkedDefs

shouldGeneralise
  :: Vector
    ( FreeV
    , ( SourceLoc
      , Concrete.TopLevelPatDefinition Concrete.Expr FreeV
      , Maybe ConcreteM
      )
    )
  -> Bool
shouldGeneralise = all (\(_, (_, def, _)) -> shouldGeneraliseDef def)
  where
    shouldGeneraliseDef (Concrete.TopLevelPatDefinition (Concrete.PatDefinition _ _ (Concrete.Clause ps _ NonEmpty.:| _))) = Vector.length ps > 0
    shouldGeneraliseDef Concrete.TopLevelPatDataDefinition {} = True
    shouldGeneraliseDef Concrete.TopLevelPatClassDefinition {} = True
    shouldGeneraliseDef Concrete.TopLevelPatInstanceDefinition {} = True

defPlicitness
  :: Concrete.TopLevelPatDefinition e v
  -> Plicitness
defPlicitness (Concrete.TopLevelPatDefinition (Concrete.PatDefinition _ IsInstance _)) = Constraint
defPlicitness Concrete.TopLevelPatDefinition {} = Explicit
defPlicitness Concrete.TopLevelPatDataDefinition {} = Explicit
defPlicitness Concrete.TopLevelPatClassDefinition {} = Explicit
defPlicitness Concrete.TopLevelPatInstanceDefinition {} = Explicit

checkTopLevelRecursiveDefs
  :: Vector
    ( QName
    , SourceLoc
    , Concrete.TopLevelPatDefinition Concrete.Expr Void
    , Maybe (Concrete.Type Void)
    )
  -> Infer
    (Vector
      ( QName
      , Definition (Abstract.Expr Void) Void
      , Abstract.Type Void Void
      )
    )
checkTopLevelRecursiveDefs defs = do
  let names = (\(v, _, _, _) -> v) <$> defs

  checkedDefs <- enterLevel $ do
    vars <- forM defs $ \(name, _, def, _) -> do
      let hint = fromQName name
      typ <- existsType hint
      forall hint (defPlicitness def) typ

    let nameIndex = hashedElemIndex names
        expose name = case nameIndex name of
          Nothing -> global name
          Just index -> pure
            $ fromMaybe (error "checkTopLevelRecursiveDefs 1")
            $ vars Vector.!? index

    let exposedDefs = flip fmap defs $ \(_, loc, def, mtyp) ->
          (loc, gbound expose $ vacuous def, gbind expose . vacuous <$> mtyp)

    checkRecursiveDefs True (Vector.zip vars exposedDefs)

  let vars' = (\(v, _, _) -> v) <$> checkedDefs

  l <- level
  let varIndex = hashedElemIndex vars'
      unexpose v = fromMaybe (pure v) $ (fmap global . (names Vector.!?)) =<< varIndex v
      vf :: FreeV -> Infer b
      vf v = internalError $ "checkTopLevelRecursiveDefs" PP.<+> shower v PP.<+> shower l
      mf :: MetaVar -> Infer b
      mf v = do
        sol <- solution v
        internalError $ "checkTopLevelRecursiveDefs" PP.<+> shower v PP.<+> "SOL" PP.<+> shower sol PP.<+> shower l

  forM (Vector.zip names checkedDefs) $ \(name, (_, def, typ)) -> do
    logDefMeta 20 ("checkTopLevelRecursiveDefs def " ++ show (pretty name)) def
    logMeta 20 ("checkTopLevelRecursiveDefs typ " ++ show (pretty name)) typ
    let unexposedDef = def >>>= unexpose
        unexposedTyp = typ >>= unexpose
    logDefMeta 20 ("checkTopLevelRecursiveDefs unexposedDef " ++ show (pretty name)) unexposedDef
    logMeta 20 ("checkTopLevelRecursiveDefs unexposedTyp " ++ show (pretty name)) unexposedTyp
    unexposedDef' <- bitraverseDefinition mf vf unexposedDef
    unexposedTyp' <- bitraverse mf vf unexposedTyp
    return (name, unexposedDef', unexposedTyp')
