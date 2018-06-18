{-# LANGUAGE OverloadedStrings #-}
module Inference.TypeCheck.Definition where

import Control.Applicative
import Control.Monad.Except
import Data.Bifunctor
import Data.Bitraversable
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.Monoid
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import {-# SOURCE #-} Inference.TypeCheck.Expr
import qualified Builtin.Names as Builtin
import Inference.Cycle
import Inference.Generalise
import Inference.MetaVar
import Inference.Monad
import Inference.TypeCheck.Clause
import Inference.TypeCheck.Data
import Inference.Unify
import MonadContext
import MonadFresh
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Pre.Scoped as Pre
import TypedFreeVar
import Util
import VIX

checkDefType
  :: Pre.PatDefinition (Pre.Clause Void Pre.Expr FreeV)
  -> CoreM
  -> Infer (Definition (Core.Expr MetaVar) FreeV, CoreM)
checkDefType (Pre.PatDefinition a i clauses) typ = do
  e' <- checkClauses clauses typ
  return (Definition a i e', typ)

checkTopLevelDefType
  :: FreeV
  -> Pre.TopLevelPatDefinition Pre.Expr FreeV
  -> SourceLoc
  -> CoreM
  -> Infer (Definition (Core.Expr MetaVar) FreeV, CoreM)
checkTopLevelDefType v def loc typ = located loc $ case def of
  Pre.TopLevelPatDefinition def' -> checkDefType def' typ
  Pre.TopLevelPatDataDefinition d -> checkDataType v d typ
  -- Should be removed by Declassify:
  Pre.TopLevelPatClassDefinition _ -> error "checkTopLevelDefType class"
  Pre.TopLevelPatInstanceDefinition _ -> error "checkTopLevelDefType instance"

checkRecursiveDefs
  :: Bool
  -> Vector
    ( FreeV
    , ( SourceLoc
      , Pre.TopLevelPatDefinition Pre.Expr FreeV
      , Maybe PreM
      )
    )
  -> Infer
    (Vector
      ( FreeV
      , Definition (Core.Expr MetaVar) FreeV
      , CoreM
      )
    )
checkRecursiveDefs forceGeneralisation defs = withDefVars $ do
  -- Divide the definitions into ones with and without type signature.
  let (noSigDefs, sigDefs) = divide defs

  -- Assume that the specified type signatures are correct.
  sigDefs' <- forM sigDefs $ \(evar, (loc, def, typ)) -> do
    typ' <- checkPoly typ Builtin.Type
    unify [] (varType evar) typ'
    return (evar, (loc, def))

  preId <- fresh

  -- The definitions without type signature are checked assuming the type
  -- signatures of the others.
  noSigResult <- checkTopLevelDefs noSigDefs

  result <- case (Vector.null sigDefs, gen) of
    (_, False) -> do
      sigResult <- checkTopLevelDefs sigDefs'
      return $ noSigResult <> sigResult
    (True, True) -> do
      -- There are no definitions with signature, so generalise the ones
      -- without signature fully
      (genNoSigResult, _) <- generaliseDefs (const True) GeneraliseAll noSigResult
      return genNoSigResult
    (False, True) -> do
      -- Generalise the definitions without signature, but don't generalise
      -- metavariables created during type-checking the type signatures above
      (genNoSigResult, noSigSub) <- generaliseDefs ((> preId) . metaId) GeneraliseAll noSigResult

      subbedSigDefs <- forM sigDefs' $ \(v, (loc, def)) -> do
        let def' = def >>>= pure . noSigSub
        return (v, (loc, def'))

      sigResult <- checkTopLevelDefs subbedSigDefs

      -- Generalise all definitions a final time, now allowing all
      -- metavariables
      (genResult, _) <- generaliseDefs (const True) GeneraliseType $ genNoSigResult <> sigResult
      return genResult

  let locs = (\(_, (loc, _)) -> loc) <$> noSigDefs
        <|> (\(_, (loc, _)) -> loc) <$> sigDefs'

  unless (Vector.length locs == Vector.length result) $
    internalError "checkRecursiveDefs unmatched length"

  let locResult = Vector.zip locs result

  detectTypeRepCycles locResult
  detectDefCycles locResult

  let permutation = Vector.zip (fst <$> defs) (fst <$> noSigDefs <|> fst <$> sigDefs)
  return $ unpermute permutation result
  where
    gen = forceGeneralisation || shouldGeneralise defs
    -- Prevent metavariables to recursively refer to the bindings in this
    -- binding group unless we know we're going to generalise
    withDefVars = if gen then withVars (fst <$> defs) else id
    divide = bimap Vector.fromList Vector.fromList . foldMap go
      where
        go (v, (loc, def, Nothing)) = ([(v, (loc, def))], [])
        go (v, (loc, def, Just t)) = ([], [(v, (loc, def, t))])

checkTopLevelDefs
  :: Vector
    ( FreeV
    , ( SourceLoc
      , Pre.TopLevelPatDefinition Pre.Expr FreeV
      )
    )
  -> Infer
    (Vector
      ( FreeV
      , Definition (Core.Expr MetaVar) FreeV
      , CoreM
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
      , Pre.TopLevelPatDefinition Pre.Expr FreeV
      , Maybe PreM
      )
    )
  -> Bool
shouldGeneralise = all (\(_, (_, def, _)) -> shouldGeneraliseDef def)
  where
    shouldGeneraliseDef (Pre.TopLevelPatDefinition (Pre.PatDefinition _ _ (Pre.Clause ps _ NonEmpty.:| _))) = Vector.length ps > 0
    shouldGeneraliseDef Pre.TopLevelPatDataDefinition {} = True
    shouldGeneraliseDef Pre.TopLevelPatClassDefinition {} = True
    shouldGeneraliseDef Pre.TopLevelPatInstanceDefinition {} = True

defPlicitness
  :: Pre.TopLevelPatDefinition e v
  -> Plicitness
defPlicitness (Pre.TopLevelPatDefinition (Pre.PatDefinition _ IsInstance _)) = Constraint
defPlicitness Pre.TopLevelPatDefinition {} = Explicit
defPlicitness Pre.TopLevelPatDataDefinition {} = Explicit
defPlicitness Pre.TopLevelPatClassDefinition {} = Explicit
defPlicitness Pre.TopLevelPatInstanceDefinition {} = Explicit

checkTopLevelRecursiveDefs
  :: Vector
    ( QName
    , SourceLoc
    , Pre.TopLevelPatDefinition Pre.Expr Void
    , Maybe (Pre.Type Void)
    )
  -> Infer
    (Vector
      ( QName
      , Definition (Core.Expr Void) Void
      , Core.Type Void Void
      )
    )
checkTopLevelRecursiveDefs defs = do
  let names = (\(v, _, _, _) -> v) <$> defs

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

  checkedDefs <- checkRecursiveDefs True (Vector.zip vars exposedDefs)

  let vars' = (\(v, _, _) -> v) <$> checkedDefs

  let varIndex = hashedElemIndex vars'
      unexpose v = fromMaybe (pure v) $ (fmap global . (names Vector.!?)) =<< varIndex v
      vf :: FreeV -> Infer b
      vf v = internalError $ "checkTopLevelRecursiveDefs" PP.<+> shower v
      mf :: MetaVar -> Infer b
      mf v = do
        sol <- solution v
        internalError $ "checkTopLevelRecursiveDefs" PP.<+> shower v PP.<+> "SOL" PP.<+> shower sol

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
