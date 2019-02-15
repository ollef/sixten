{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Elaboration.TypeCheck.Data where

import Protolude hiding (typeRep)

import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Driver.Query
import Effect
import qualified Effect.Context as Context
import Elaboration.Constraint as Constraint
import Elaboration.MetaVar
import Elaboration.MetaVar.Zonk
import Elaboration.Monad
import Elaboration.TypeCheck.Expr
import Elaboration.Unify
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Pre.Scoped as Pre
import qualified TypeRep

checkDataDef
  :: FreeVar
  -> DataDef Pre.Expr FreeVar
  -> CoreM
  -> Elaborate (DataDef (Core.Expr MetaVar) FreeVar, CoreM)
checkDataDef var (DataDef ps cs) typ =
  -- TODO: These vars are typechecked twice (in checkAndGeneraliseDefs as the
-- expected type and here). Can we clean this up?
  teleMapExtendContext ps (`checkPoly` Builtin.Type) $ \vs -> do
    typ' <- Core.pis vs Builtin.Type
    runUnify (unify [] typ' typ) report

    let
      pvs = Vector.zipWith (\p v -> (p, pure v)) (telePlics ps) vs
      constrRetType = Core.apps (pure var) pvs

    (cs', sizes) <- fmap unzip $ forM cs $ \(ConstrDef c t) ->
      checkConstrDef (ConstrDef c $ instantiateTele pure vs t) constrRetType

    intRep <- fetchIntRep

    let tagRep = case cs of
          [] -> TypeRep.UnitRep
          [_] -> TypeRep.UnitRep
          _ -> intRep

        typeRep
          = productType (Core.MkType tagRep)
          $ foldl' sumType (Core.MkType TypeRep.UnitRep) sizes

    forM_ cs' $ \(ConstrDef qc e) ->
      logMeta "tc.data" ("checkDataDef res " ++ show qc) $ zonk e

    typeRep' <- whnfExpandingTypeReps typeRep
    logMeta "tc.data" "checkDataDef typeRep" $ zonk typeRep'

    result <- dataDef vs cs'
    paramTypeRep <- Core.lams vs typeRep'
    return (result, paramTypeRep)

checkConstrDef
  :: ConstrDef PreM
  -> CoreM
  -> Elaborate (ConstrDef CoreM, CoreM)
checkConstrDef (ConstrDef c ctype) retType = do
  logPretty "tc.def.constr" "checkConstrDef constr" $ pure c
  ctype' <- checkPoly ctype Builtin.Type
  logMeta "tc.def.constr" "checkConstrDef ctype" $ zonk ctype'
  sizes <- go ctype'
  let size = foldl' productType (Core.MkType TypeRep.UnitRep) sizes
  logMeta "tc.def.constr" "checkConstrDef size" $ zonk size
  return (ConstrDef c ctype', size)
  where
    -- TODO: Check for escaping type variables and improve error message
    go t = do
      t' <- whnf t
      go' t'
    go' (Core.Pi h p t s) = do
      rep <- whnfExpandingTypeReps t
      Context.freshExtend (binding h p t) $ \v -> do
        sizes <- go $ instantiate1 (pure v) s
        return $ rep : sizes
    go' ret = do
      runUnify (unify [] retType ret) report
      return []

-------------------------------------------------------------------------------
-- Type helpers
productType :: Core.Expr m v -> Core.Expr m v -> Core.Expr m v
productType (Core.MkType TypeRep.UnitRep) e = e
productType e (Core.MkType TypeRep.UnitRep) = e
productType (Core.MkType a) (Core.MkType b) = Core.MkType $ TypeRep.product a b
productType a b = Builtin.ProductTypeRep a b

sumType :: Core.Expr m v -> Core.Expr m v -> Core.Expr m v
sumType (Core.MkType TypeRep.UnitRep) e = e
sumType e (Core.MkType TypeRep.UnitRep) = e
sumType (Core.MkType a) (Core.MkType b) = Core.MkType $ TypeRep.sum a b
sumType a b = Builtin.SumTypeRep a b
