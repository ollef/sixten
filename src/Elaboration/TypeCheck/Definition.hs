{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings #-}
module Elaboration.TypeCheck.Definition where

import Protolude

import Data.Vector(Vector)
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Effect
import qualified Effect.Context as Context
import Effect.Log as Log
import Elaboration.Generalise
import Elaboration.MetaVar
import Elaboration.MetaVar.Zonk
import Elaboration.Monad
import Elaboration.TypeCheck.Class
import Elaboration.TypeCheck.Clause
import Elaboration.TypeCheck.Data
import Elaboration.TypeCheck.Expr
import Elaboration.Unify
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Pre.Scoped as Pre
import Util

checkAndGeneraliseTopLevelDefs
  :: Vector
    ( QName
    , SourceLoc
    , Closed (Pre.Definition Pre.Expr)
    )
  -> Elaborate
    (Vector
      ( GName
      , SourceLoc
      , ClosedDefinition Core.Expr
      , Biclosed Core.Type
      )
    )
checkAndGeneraliseTopLevelDefs defs = do
  varDefs <- forM defs $ \(name, loc, def) -> do
    var <- Context.freeVar
    typ <- existsType $ fromQName name
    return (var, name, loc, def, typ)

  let
    lookupNameVar = hashedLookup [(name, var) | (var, name, _, _, _) <- varDefs]
    expose name = maybe (global name) pure $ lookupNameVar name

    exposedDefs = [(var, name, loc, gbound expose $ open def, typ) | (var, name, loc, def, typ) <- varDefs]

  checkedDefs <- checkAndGeneraliseDefs exposedDefs

  let
    varNames = (\(var, name, _, _, _) -> (var, name)) <$> checkedDefs
    lookupVarName = hashedLookup varNames
    unexpose v = maybe (pure v) global $ lookupVarName v
    defBindings = foreach checkedDefs $ \(v, n, _, _, t) ->
      (v, binding (fromGName n) Explicit t)

  Context.extends defBindings $ do -- for printing
    logPretty "tc.def" "checkAndGeneraliseTopLevelDefs context" $ Context.extends defBindings $ Context.prettyContext prettyMeta
    forM checkedDefs $ \(_, name, loc, def, typ) -> do
      -- logDefMeta 20 ("checkAndGeneraliseTopLevelDefs def " ++ show (pretty name)) def
      logMeta "tc.def" ("checkAndGeneraliseTopLevelDefs typ " ++ show (pretty name)) $ Context.extends defBindings $ zonk typ
      let
        unexposedDef = def >>>= unexpose
        unexposedTyp = typ >>= unexpose
      -- logDefMeta "tc.def" ("checkAndGeneraliseTopLevelDefs unexposedDef " ++ show (pretty name)) unexposedDef
      logMeta "tc.def" ("checkAndGeneraliseTopLevelDefs unexposedTyp " ++ show (pretty name)) $ Context.extends defBindings $ zonk unexposedTyp
      return (name, loc, closeDefinition noMeta noVar unexposedDef, biclose noMeta noVar unexposedTyp)
  where
    noVar :: FreeVar -> b
    noVar v = panic $ "checkAndGeneraliseTopLevelDefs " <> shower v
    noMeta :: MetaVar -> b
    noMeta v = panic
      $ "checkAndGeneraliseTopLevelDefs " <> shower v

checkAndGeneraliseDefs
  :: Vector
    ( FreeVar
    , QName
    , SourceLoc
    , Pre.Definition Pre.Expr FreeVar
    , CoreM
    )
  -> Elaborate
    (Vector
      ( FreeVar
      , GName
      , SourceLoc
      , Definition (Core.Expr MetaVar) FreeVar
      , CoreM
      )
    )
checkAndGeneraliseDefs defs = do
  let
    defBindings = foreach defs $ \(v, n, _, d, t) -> (v, binding (fromQName n) (defPlicitness d) t)
  Context.extends defBindings $ do
    -- Divide the definitions into ones with and without type signature.
    let
      (noSigDefs, sigDefs) = divide defs

    -- Assume that the specified type signatures are correct.
    sigDefs' <- forM sigDefs $ \(var, name, loc, def, typ) -> do
      typ' <- checkPoly typ Builtin.Type
      varType <- Context.lookupType var
      runUnify (unify [] varType typ') report
      return (var, name, loc, def)

    preId <- fresh

    -- The definitions without type signature are checked assuming the type
    -- signatures of the others.
    (noSigResult, noSigDesugar) <- checkDefs noSigDefs

    let
      noSigDesugarBindings = foreach noSigDesugar $ \(v, n, _, _, t) -> (v, binding (fromGName n) Explicit t)
      noSigDesugar' = foreach noSigDesugar $ \(v, n, l, d, _) -> (v, n, l, d)
      noSigResult' = noSigResult <> noSigDesugar'

    Context.extends noSigDesugarBindings $
      if Vector.null sigDefs then
          -- There are no definitions with signature, so generalise the ones
          -- without signature fully
          generaliseDefs (const True) GeneraliseAll noSigResult'
        else do
          -- Generalise the definitions without signature, but don't generalise
          -- metavariables created during type-checking the type signatures above
          genNoSigResult <- generaliseDefs ((> preId) . metaId) GeneraliseAll noSigResult'

          let
            genNoSigBindingUpdates = foreach genNoSigResult $ \(v, _, _, _, t) -> (v, \b -> b { Context._type = t })

          Context.updates genNoSigBindingUpdates $ do
            (sigResult, sigDesugar) <- checkDefs sigDefs'
            let
              sigDesugarBindings = foreach sigDesugar $ \(v, n, _, _, t) -> (v, binding (fromGName n) Explicit t)
              sigDesugar' = foreach sigDesugar $ \(v, n, l, d, _) -> (v, n, l, d)
              sigResult' = sigResult <> sigDesugar'
              genNoSigResult' = foreach genNoSigResult $ \(v, n, l, d, _) -> (v, n, l, d)

            -- Generalise all definitions a final time, now allowing all
            -- metavariables
            Context.extends sigDesugarBindings $
              generaliseDefs (const True) GeneraliseType $ genNoSigResult' <> sigResult'
  where
    -- Prevent metavariables to recursively refer to the bindings in this
    -- binding group unless we know we're going to generalise
    divide = bimap Vector.fromList Vector.fromList . foldMap go
      where
        go (v, name, loc, def@(Pre.ConstantDefinition (Pre.ConstantDef _ _ (Just typ))), _) = ([], [(v, name, loc, def, typ)])
        go (v, name, loc, def@(Pre.ConstantDefinition (Pre.ConstantDef _ _ Nothing)), _) = ([(v, name, loc, def)], [])
        go (v, name, loc, def@(Pre.DataDefinition (DataDef tele _)), _) = ([], [(v, name, loc, def, Pre.telePis tele $ Pre.Global Builtin.TypeName)])
        go (v, name, loc, def@(Pre.ClassDefinition (ClassDef tele _)), _) = ([], [(v, name, loc, def, Pre.telePis tele $ Pre.Global Builtin.TypeName)])
        go (v, name, loc, def@(Pre.InstanceDefinition (Pre.InstanceDef typ _)), _) = ([], [(v, name, loc, def, typ)])

checkDefs
  :: Vector
    ( FreeVar
    , QName
    , SourceLoc
    , Pre.Definition Pre.Expr FreeVar
    )
  -> Elaborate
    ( Vector (FreeVar, GName, SourceLoc, Definition (Core.Expr MetaVar) FreeVar)
    , Vector (FreeVar, GName, SourceLoc, Definition (Core.Expr MetaVar) FreeVar, CoreM)
    )
checkDefs defs = Log.indent $ do
  results <- forM defs $ \(var, name, loc, def) -> do
    typ <- Context.lookupType var
    located loc $ checkDef var name loc def typ
  let (defs', generatedDefs) = Vector.unzip results
  return (defs', join generatedDefs)

checkDef
  :: FreeVar
  -> QName
  -> SourceLoc
  -> Pre.Definition Pre.Expr FreeVar
  -> CoreM
  -> Elaborate
    ( (FreeVar, GName, SourceLoc, Definition (Core.Expr MetaVar) FreeVar)
    , Vector (FreeVar, GName, SourceLoc, Definition (Core.Expr MetaVar) FreeVar, CoreM)
    )
checkDef v name loc def typ = do
  logPretty "tc.def" "Checking definition" $ pure name
  case def of
    Pre.ConstantDefinition d -> do
      (a, e) <- checkConstantDef d typ
      return ((v, gname name, loc, ConstantDefinition a e), mempty)
    Pre.DataDefinition d -> do
      (d', rep) <- checkDataDef v d typ
      return ((v, gname name, loc, DataDefinition d' rep), mempty)
    Pre.ClassDefinition d -> do
      d' <- checkClassDef d typ
      desugarClassDef v name loc d'
    Pre.InstanceDefinition d ->
      checkInstance v name loc d typ

defPlicitness
  :: Pre.Definition e v
  -> Plicitness
defPlicitness Pre.ConstantDefinition {} = Explicit
defPlicitness Pre.DataDefinition {} = Explicit
defPlicitness Pre.ClassDefinition {} = Explicit
defPlicitness Pre.InstanceDefinition {} = Constraint
