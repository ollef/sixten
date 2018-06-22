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

checkAndGeneraliseDefs
  :: Bool
  -> Vector
    ( FreeV
    , ( SourceLoc
      , Pre.Definition Pre.Expr FreeV
      )
    )
  -> Infer
    (Vector
      ( FreeV
      , Definition (Core.Expr MetaVar) FreeV
      )
    )
checkAndGeneraliseDefs forceGeneralisation defs = withDefVars $ do
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
  noSigResult <- checkDefs noSigDefs

  result <- case (Vector.null sigDefs, gen) of
    (_, False) -> do
      sigResult <- checkDefs sigDefs'
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

      sigResult <- checkDefs subbedSigDefs

      -- Generalise all definitions a final time, now allowing all
      -- metavariables
      (genResult, _) <- generaliseDefs (const True) GeneraliseType $ genNoSigResult <> sigResult
      return genResult

  let locs = (\(_, (loc, _)) -> loc) <$> noSigDefs
        <|> (\(_, (loc, _)) -> loc) <$> sigDefs'

  unless (Vector.length locs == Vector.length result) $
    internalError "checkAndGeneraliseDefs unmatched length"

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
        go (v, (loc, def@(Pre.ConstantDefinition (Pre.ConstantDef _ _ _ (Just typ))))) = ([], [(v, (loc, def, typ))])
        go (v, (loc, def@(Pre.ConstantDefinition (Pre.ConstantDef _ _ _ Nothing)))) = ([(v, (loc, def))], [])
        go (v, (loc, def@(Pre.DataDefinition (DataDef tele _)))) = ([], [(v, (loc, def, Pre.telePis tele $ Pre.Global Builtin.TypeName))])
        go _ = error "checkAndGeneraliseDefs divide"

checkDef
  :: FreeV
  -> Pre.Definition Pre.Expr FreeV
  -> Infer (Definition (Core.Expr MetaVar) FreeV)
checkDef v def = case def of
  Pre.ConstantDefinition def' -> checkConstantDef def' $ varType v
  Pre.DataDefinition d -> checkDataDef v d
  -- Should be removed by Declassify:
  Pre.ClassDefinition _ -> error "checkDef class"
  Pre.InstanceDefinition _ -> error "checkDef instance"

checkDefs
  :: Vector
    ( FreeV
    , ( SourceLoc
      , Pre.Definition Pre.Expr FreeV
      )
    )
  -> Infer
    (Vector
      ( FreeV
      , Definition (Core.Expr MetaVar) FreeV
      )
    )
checkDefs defs = indentLog $
  forM defs $ \(var, (loc, def)) -> do
    def' <- located loc $ checkDef var def
    return (var, def')

checkAndGeneraliseTopLevelDefs
  :: Vector
    ( QName
    , SourceLoc
    , Pre.Definition Pre.Expr Void
    )
  -> Infer
    (Vector
      ( QName
      , Definition (Core.Expr Void) Void
      , Core.Type Void Void
      )
    )
checkAndGeneraliseTopLevelDefs defs = do
  let names = (\(v, _, _) -> v) <$> defs

  vars <- forM defs $ \(name, _, def) -> do
    let hint = fromQName name
    typ <- existsType hint
    forall hint (defPlicitness def) typ

  let nameIndex = hashedElemIndex names
      expose name = case nameIndex name of
        Nothing -> global name
        Just index -> pure
          $ fromMaybe (error "checkAndGeneraliseTopLevelDefs 1")
          $ vars Vector.!? index

  let exposedDefs = flip fmap defs $ \(_, loc, def) ->
        (loc, gbound expose $ vacuous def)

  checkedDefs <- checkAndGeneraliseDefs True (Vector.zip vars exposedDefs)

  let vars' = fst <$> checkedDefs

  let varIndex = hashedElemIndex vars'
      unexpose v = fromMaybe (pure v) $ (fmap global . (names Vector.!?)) =<< varIndex v
      vf :: FreeV -> Infer b
      vf v = internalError $ "checkAndGeneraliseTopLevelDefs" PP.<+> shower v
      mf :: MetaVar -> Infer b
      mf v = do
        sol <- solution v
        internalError $ "checkAndGeneraliseTopLevelDefs" PP.<+> shower v PP.<+> "SOL" PP.<+> shower sol

  forM (Vector.zip names checkedDefs) $ \(name, (v, def)) -> do
    let typ = varType v
    logDefMeta 20 ("checkAndGeneraliseTopLevelDefs def " ++ show (pretty name)) def
    logMeta 20 ("checkAndGeneraliseTopLevelDefs typ " ++ show (pretty name)) typ
    let unexposedDef = def >>>= unexpose
        unexposedTyp = typ >>= unexpose
    logDefMeta 20 ("checkAndGeneraliseTopLevelDefs unexposedDef " ++ show (pretty name)) unexposedDef
    logMeta 20 ("checkAndGeneraliseTopLevelDefs unexposedTyp " ++ show (pretty name)) unexposedTyp
    unexposedDef' <- bitraverseDefinition mf vf unexposedDef
    unexposedTyp' <- bitraverse mf vf unexposedTyp
    return (name, unexposedDef', unexposedTyp')

shouldGeneralise
  :: Vector
    ( FreeV
    , ( SourceLoc
      , Pre.Definition Pre.Expr FreeV
      )
    )
  -> Bool
shouldGeneralise = all (\(_, (_, def)) -> shouldGeneraliseDef def)
  where
    shouldGeneraliseDef (Pre.ConstantDefinition (Pre.ConstantDef _ _ (Pre.Clause ps _ NonEmpty.:| _) _)) = Vector.length ps > 0
    shouldGeneraliseDef Pre.DataDefinition {} = True
    shouldGeneraliseDef Pre.ClassDefinition {} = True
    shouldGeneraliseDef Pre.InstanceDefinition {} = True

defPlicitness
  :: Pre.Definition e v
  -> Plicitness
defPlicitness (Pre.ConstantDefinition (Pre.ConstantDef _ IsInstance _ _)) = Constraint
defPlicitness Pre.ConstantDefinition {} = Explicit
defPlicitness Pre.DataDefinition {} = Explicit
defPlicitness Pre.ClassDefinition {} = Explicit
defPlicitness Pre.InstanceDefinition {} = Explicit
