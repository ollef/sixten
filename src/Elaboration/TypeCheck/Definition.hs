{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings #-}
module Elaboration.TypeCheck.Definition where

import Protolude

import Data.Vector(Vector)
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Effect
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
    let hint = fromQName name
    typ <- existsType hint
    var <- forall hint (defPlicitness $ open def) typ
    return (var, name, loc, def)

  let lookupNameVar = hashedLookup [(name, var) | (var, name, _, _) <- varDefs]
      expose name = maybe (global name) pure $ lookupNameVar name

      exposedDefs = [(var, name, loc, gbound expose $ open def) | (var, name, loc, def) <- varDefs]

  checkedDefs <- checkAndGeneraliseDefs exposedDefs

  let varNames = (\(var, name, _, _) -> (var, name)) <$> checkedDefs
      lookupVarName = hashedLookup varNames
      unexpose v = maybe (pure v) global $ lookupVarName v

  forM checkedDefs $ \(v, name, loc, def) -> do
    let typ = varType v
    -- logDefMeta 20 ("checkAndGeneraliseTopLevelDefs def " ++ show (pretty name)) def
    logMeta "tc.def" ("checkAndGeneraliseTopLevelDefs typ " ++ show (pretty name)) $ zonk typ
    let unexposedDef = def >>>= unexpose
        unexposedTyp = typ >>= unexpose
    -- logDefMeta "tc.def" ("checkAndGeneraliseTopLevelDefs unexposedDef " ++ show (pretty name)) unexposedDef
    logMeta "tc.def" ("checkAndGeneraliseTopLevelDefs unexposedTyp " ++ show (pretty name)) $ zonk unexposedTyp
    return (name, loc, closeDefinition noMeta noVar unexposedDef, biclose noMeta noVar unexposedTyp)
  where
    noVar :: FreeV -> b
    noVar v = panic $ "checkAndGeneraliseTopLevelDefs " <> shower v
    noMeta :: MetaVar -> b
    noMeta v = panic
      $ "checkAndGeneraliseTopLevelDefs " <> shower v

checkAndGeneraliseDefs
  :: Vector
    ( FreeV
    , QName
    , SourceLoc
    , Pre.Definition Pre.Expr FreeV
    )
  -> Elaborate
    (Vector
      ( FreeV
      , GName
      , SourceLoc
      , Definition (Core.Expr MetaVar) FreeV
      )
    )
checkAndGeneraliseDefs defs = withVars ((\(v, _, _, _) -> v) <$> defs) $ do
  -- Divide the definitions into ones with and without type signature.
  let (noSigDefs, sigDefs) = divide defs

  -- Assume that the specified type signatures are correct.
  sigDefs' <- forM sigDefs $ \(var, name, loc, def, typ) -> do
    typ' <- checkPoly typ Builtin.Type
    runUnify (unify [] (varType var) typ') report
    return (var, name, loc, def)

  preId <- fresh

  -- The definitions without type signature are checked assuming the type
  -- signatures of the others.
  noSigResult <- checkDefs noSigDefs

  if Vector.null sigDefs then do
      -- There are no definitions with signature, so generalise the ones
      -- without signature fully
      (genNoSigResult, _) <- generaliseDefs (const True) GeneraliseAll noSigResult
      return genNoSigResult
    else do
      -- Generalise the definitions without signature, but don't generalise
      -- metavariables created during type-checking the type signatures above
      (genNoSigResult, noSigSub) <- generaliseDefs ((> preId) . metaId) GeneraliseAll noSigResult

      subbedSigDefs <- forM sigDefs' $ \(v, name, loc, def) -> do
        let def' = def >>>= pure . noSigSub
        return (v, name, loc, def')

      sigResult <- checkDefs subbedSigDefs

      -- Generalise all definitions a final time, now allowing all
      -- metavariables
      (genResult, _) <- generaliseDefs (const True) GeneraliseType $ genNoSigResult <> sigResult
      return genResult
  where
    -- Prevent metavariables to recursively refer to the bindings in this
    -- binding group unless we know we're going to generalise
    divide = bimap Vector.fromList Vector.fromList . foldMap go
      where
        go (v, name, loc, def@(Pre.ConstantDefinition (Pre.ConstantDef _ _ (Just typ)))) = ([], [(v, name, loc, def, typ)])
        go (v, name, loc, def@(Pre.ConstantDefinition (Pre.ConstantDef _ _ Nothing))) = ([(v, name, loc, def)], [])
        go (v, name, loc, def@(Pre.DataDefinition (DataDef tele _))) = ([], [(v, name, loc, def, Pre.telePis tele $ Pre.Global Builtin.TypeName)])
        go (v, name, loc, def@(Pre.ClassDefinition (ClassDef tele _))) = ([], [(v, name, loc, def, Pre.telePis tele $ Pre.Global Builtin.TypeName)])
        go (v, name, loc, def@(Pre.InstanceDefinition (Pre.InstanceDef typ _))) = ([], [(v, name, loc, def, typ)])

checkDefs
  :: Vector
    ( FreeV
    , QName
    , SourceLoc
    , Pre.Definition Pre.Expr FreeV
    )
  -> Elaborate
    (Vector
      ( FreeV
      , GName
      , SourceLoc
      , Definition (Core.Expr MetaVar) FreeV
      )
    )
checkDefs defs = Log.indent $
  fmap join $ forM defs $ \(var, name, loc, def) ->
    located loc $ checkDef var name loc def

checkDef
  :: FreeV
  -> QName
  -> SourceLoc
  -> Pre.Definition Pre.Expr FreeV
  -> Elaborate (Vector (FreeV, GName, SourceLoc, Definition (Core.Expr MetaVar) FreeV))
checkDef v name loc def = case def of
  Pre.ConstantDefinition d -> do
    (a, e) <- checkConstantDef d $ varType v
    return $ pure (v, gname name, loc, ConstantDefinition a e)
  Pre.DataDefinition d -> do
    (d', rep) <- checkDataDef v d
    return $ pure (v, gname name, loc, DataDefinition d' rep)
  Pre.ClassDefinition d -> do
    d' <- checkClassDef v d
    desugarClassDef v name loc d'
  Pre.InstanceDefinition d ->
    checkInstance v name loc d

defPlicitness
  :: Pre.Definition e v
  -> Plicitness
defPlicitness Pre.ConstantDefinition {} = Explicit
defPlicitness Pre.DataDefinition {} = Explicit
defPlicitness Pre.ClassDefinition {} = Explicit
defPlicitness Pre.InstanceDefinition {} = Constraint
