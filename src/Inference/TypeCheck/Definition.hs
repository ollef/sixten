{-# LANGUAGE OverloadedStrings #-}
module Inference.TypeCheck.Definition where

import Control.Applicative
import Control.Monad.Except
import Data.Bifunctor
import Data.Foldable as Foldable
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.Monoid
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import {-# SOURCE #-} Inference.TypeCheck.Expr
import qualified Builtin.Names as Builtin
import Inference.Constraint
import Inference.Cycle
import Inference.Meta
import Inference.Monad
import Inference.TypeCheck.Clause
import Inference.TypeCheck.Data
import Inference.Unify
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete.Scoped as Concrete
import Util
import Util.TopoSort
import VIX

checkDefType
  :: Concrete.PatDefinition (Concrete.Clause Void Concrete.Expr MetaA)
  -> AbstractM
  -> Infer (Definition Abstract.Expr MetaA, AbstractM)
checkDefType (Concrete.PatDefinition a i clauses) typ = do
  e' <- checkClauses clauses typ
  return (Definition a i e', typ)

checkTopLevelDefType
  :: MetaA
  -> Concrete.TopLevelPatDefinition Concrete.Expr MetaA
  -> SourceLoc
  -> AbstractM
  -> Infer (Definition Abstract.Expr MetaA, AbstractM)
checkTopLevelDefType v def loc typ = located loc $ case def of
  Concrete.TopLevelPatDefinition def' -> checkDefType def' typ
  Concrete.TopLevelPatDataDefinition d -> checkDataType v d typ
  -- Should be removed by Declassify:
  Concrete.TopLevelPatClassDefinition _ -> error "checkTopLevelDefType class"
  Concrete.TopLevelPatInstanceDefinition _ -> error "checkTopLevelDefType instance"

generaliseDef
  :: Foldable t
  => t (Plicitness, MetaA)
  -> Definition Abstract.Expr MetaA
  -> AbstractM
  -> Infer (Definition Abstract.Expr MetaA, AbstractM)
generaliseDef vs (Definition a i e) t = do
  ge <- abstractMs vs Abstract.Lam e
  gt <- abstractMs vs Abstract.Pi t
  return (Definition a i ge, gt)
generaliseDef vs (DataDefinition (DataDef cs) rep) typ = do
  let cs' = map (fmap $ toScope . splat f g) cs
  -- Abstract vs on top of typ
  grep <- abstractMs vs Abstract.Lam rep
  gtyp <- abstractMs vs Abstract.Pi typ
  return (DataDefinition (DataDef cs') grep, gtyp)
  where
    varIndex = hashedElemIndex $ snd <$> toVector vs
    f v = pure $ maybe (F v) (B . TeleVar) (varIndex v)
    g = pure . B . (+ TeleVar (length vs))

abstractMs
  :: Foldable t
  => t (Plicitness, MetaA)
  -> (NameHint -> Plicitness -> AbstractM -> ScopeM () Abstract.Expr -> AbstractM)
  -> AbstractM
  -> Infer AbstractM
abstractMs vs c b = foldrM
  (\(p, v)  s -> c (metaHint v) p (metaType v) <$> abstract1M v s)
  b
  vs

data GeneraliseDefsMode
  = GeneraliseType
  | GeneraliseAll
  deriving (Eq, Show)

generaliseDefs
  :: GeneraliseDefsMode
  -> Vector
    ( MetaA
    , Definition Abstract.Expr MetaA
    , AbstractM
    )
  -> Infer
    ( Vector
      ( MetaA
      , Definition Abstract.Expr MetaA
      , AbstractM
      )
    , MetaA -> MetaA
    )
generaliseDefs mode defs = do
  -- After type-checking we may actually be in a situation where a dependency
  -- we thought existed doesn't actually exist because of class instances being
  -- resolved (unresolved class instances are assumed to depend on all
  -- instances), so we can't be sure that we have a single cycle. Therefore we
  -- separately compute dependencies for each definition.
  modifyIndent succ

  let vars = (\(v, _, _) -> v) <$> defs

  defFreeVars <- case mode of
    GeneraliseType -> forM defs $ \_ -> return mempty
    GeneraliseAll -> forM defs $ \(_, def, _) ->
      foldMapMetas HashSet.singleton def

  typeFreeVars <- forM defs $ \(_, _, t) ->
    foldMapMetas HashSet.singleton t

  mergeConstraintVars $ HashSet.unions $ toList $ defFreeVars <> typeFreeVars

  l <- level

  let sat p freeVars = do
        let freeVarsMap = HashMap.fromList $ toList $ Vector.zip vars freeVars
        forM freeVars $ \fvs -> do
          let fvs' = saturate (\v -> HashMap.lookupDefault (HashSet.singleton v) v freeVarsMap) fvs
          fmap HashSet.fromList $ filterM p $ HashSet.toList fvs'

      isLocalConstraint v@MetaVar { metaData = Constraint } = isLocalExists v
      isLocalConstraint _ = return False

      isLocalExists MetaVar { metaRef = Exists r } = either (>= l) (const False) <$> solution r
      isLocalExists MetaVar { metaRef = Forall } = return False
      isLocalExists MetaVar { metaRef = LetRef {} } = return False

  satDefFreeVars <- sat isLocalConstraint defFreeVars
  satTypeFreeVars <- sat isLocalExists typeFreeVars

  let freeVars = Vector.zipWith (<>) satDefFreeVars satTypeFreeVars

  sortedFreeVars <- forM freeVars $ \fvs -> do

    deps <- forM (HashSet.toList fvs) $ \v -> do
      ds <- foldMapMetas HashSet.singleton $ metaType v
      return (v, ds)

    let sortedFvs = acyclic <$> topoSort deps

    return [(implicitise $ metaData fv, fv) | fv <- sortedFvs]

  let lookupFreeVars = hashedLookup $ Vector.zip vars sortedFreeVars
      sub v = maybe (pure v) (Abstract.apps (pure v) . fmap (second pure)) $ lookupFreeVars v

  instDefs <- forM defs $ \(v, d, t) -> do
    d' <- boundM (return . sub) d
    t' <- bindM (return . sub) t
    return (v, d', t')

  genDefs <- forM (Vector.zip sortedFreeVars instDefs) $ \(fvs, (v, d, t)) -> do
    (d', t') <- generaliseDef fvs d t
    return (v, d', t')

  newVars <- forM genDefs $ \(v, _, t) ->
    forall (metaHint v) (metaData v) t

  let lookupNewVar = hashedLookup $ Vector.zip vars newVars
      newVarSub v = fromMaybe v $ lookupNewVar v

  newVarDefs <- forM (Vector.zip newVars genDefs) $ \(v, (_, d, t)) -> do
    d' <- boundM (return . pure . newVarSub) d
    t' <- bindM (return . pure . newVarSub) t
    return (v, d', t')

  modifyIndent pred

  return (newVarDefs, newVarSub)
  where
    acyclic (AcyclicSCC a) = a
    acyclic (CyclicSCC _) = error "generaliseDefs"

checkRecursiveDefs
  :: Bool
  -> Vector
    ( MetaA
    , ( SourceLoc
      , Concrete.TopLevelPatDefinition Concrete.Expr MetaA
      , Maybe ConcreteM
      )
    )
  -> Infer
    (Vector
      ( MetaA
      , Definition Abstract.Expr MetaA
      , AbstractM
      )
    )
checkRecursiveDefs forceGeneralisation defs = do
  let localInstances
        = flip Vector.mapMaybe defs
        $ \(v, (_, def, _)) -> case def of
          Concrete.TopLevelPatDefinition (Concrete.PatDefinition _ IsInstance _) -> Just v { metaData = Constraint }
          _ -> Nothing
  withVars localInstances $ do
    -- Divide the definitions into ones with and without type signature.
    let (noSigDefs, sigDefs) = divide defs

    -- Assume that the specified type signatures are correct.
    sigDefs' <- forM sigDefs $ \(evar, (loc, def, typ)) -> do
      typ' <- checkPoly typ Builtin.Type
      unify [] (metaType evar) typ'
      return (evar, (loc, def))

    -- The definitions without type signature are checked and generalised,
    -- assuming the type signatures of the others.
    noSigResult <- checkAndElabDefs noSigDefs

    result <- if forceGeneralisation || shouldGeneralise defs then do

      -- Generalise the definitions without signature
      (genNoSigResult, noSigSub) <- generaliseDefs GeneraliseAll noSigResult

      subbedSigDefs <- forM sigDefs' $ \(v, (loc, def)) -> do
        let def' = bound (pure . noSigSub) global def
        return (v, (loc, def'))

      sigResult <- checkAndElabDefs subbedSigDefs

      -- Generalise the definitions with signature
      if Vector.null sigResult then
          -- No need to generalise again if there are actually no definitions
          -- with signatures
          return genNoSigResult
        else do
          (genResult, _) <- generaliseDefs GeneraliseType $ genNoSigResult <> sigResult
          return genResult
    else do
      sigResult <- checkAndElabDefs sigDefs'
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

checkAndElabDefs
  :: Vector
    ( MetaA
    , ( SourceLoc
      , Concrete.TopLevelPatDefinition Concrete.Expr MetaA
      )
    )
  -> Infer
    (Vector
      ( MetaA
      , Definition Abstract.Expr MetaA
      , AbstractM
      )
    )
checkAndElabDefs defs = do
  forM_ defs $ \(evar, (_, def)) ->
    logMeta 20 ("checkAndElabDefs " ++ show (pretty $ fromNameHint "" id $ metaHint evar)) def

  modifyIndent succ

  checkedDefs <- forM defs $ \(evar, (loc, def)) -> do
    (def', typ'') <- checkTopLevelDefType evar def loc $ metaType evar
    return (loc, (evar, def', typ''))

  elabDefs <- elabRecursiveDefs $ snd <$> checkedDefs

  modifyIndent pred

  forM_ elabDefs $ \(evar, def, typ) -> do
    logMeta 20 ("checkAndElabDefs res " ++ show (pretty $ fromNameHint "" id $ metaHint evar)) def
    logMeta 20 ("checkAndElabDefs res t " ++ show (pretty $ fromNameHint "" id $ metaHint evar)) typ

  return elabDefs

shouldGeneralise
  :: Vector
    ( MetaA
    , ( SourceLoc
      , Concrete.TopLevelPatDefinition Concrete.Expr MetaA
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
      , Definition Abstract.Expr Void
      , Abstract.Type Void
      )
    )
checkTopLevelRecursiveDefs defs = do
  let names = (\(v, _, _, _) -> v) <$> defs

  checkedDefs <- enterLevel $ do
    evars <- forM names $ \name -> do
      let hint = fromQName name
      typ <- existsType hint
      forall hint Explicit typ

    let nameIndex = hashedElemIndex names
        expose name = case nameIndex name of
          Nothing -> global name
          Just index -> pure
            $ fromMaybe (error "checkTopLevelRecursiveDefs 1")
            $ evars Vector.!? index

    let exposedDefs = flip fmap defs $ \(_, loc, def, mtyp) ->
          (loc, bound absurd expose def, bind absurd expose <$> mtyp)

    checkRecursiveDefs True (Vector.zip evars exposedDefs)

  let evars' = (\(v, _, _) -> v) <$> checkedDefs

  let varIndex = hashedElemIndex evars'
      unexpose v = fromMaybe (pure v) $ (fmap global . (names Vector.!?)) =<< varIndex v
      vf :: MetaA -> Infer b
      vf v = internalError $ "checkTopLevelRecursiveDefs" PP.<+> shower v

  forM (Vector.zip names checkedDefs) $ \(name, (_, def, typ)) -> do
    unexposedDef <- boundM (pure . unexpose) def
    unexposedTyp <- bindM (pure . unexpose) typ
    logMeta 20 ("checkTopLevelRecursiveDefs unexposedDef " ++ show (pretty name)) unexposedDef
    logMeta 20 ("checkTopLevelRecursiveDefs unexposedTyp " ++ show (pretty name)) unexposedTyp
    unexposedDef' <- traverse vf unexposedDef
    unexposedTyp' <- traverse vf unexposedTyp
    return (name, unexposedDef', unexposedTyp')

