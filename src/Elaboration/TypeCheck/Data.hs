{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Elaboration.TypeCheck.Data where

import Protolude hiding (typeRep)

import Data.Vector(Vector)
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Driver.Query
import Effect
import qualified Effect.Context as Context
import Elaboration.Constraint as Constraint
import Elaboration.MetaVar
import Elaboration.MetaVar.Zonk
import Elaboration.Monad
import Elaboration.TypeOf
import Elaboration.TypeCheck.Expr
import qualified Elaboration.Equal as Equal
import Elaboration.Unify
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Pre.Scoped as Pre
import qualified TypeRep
import Util

checkDataDef
  :: Var
  -> DataDef Pre.Expr Var
  -> CoreM
  -> Elaborate (DataDef (Core.Expr MetaVar) Var, CoreM)
checkDataDef var (DataDef b ps cs) typ =
  -- TODO: These vars are typechecked twice (in checkAndGeneraliseDefs as the
-- expected type and here). Can we clean this up?
  teleMapExtendContext ps (`checkPoly` Builtin.Type) $ \vs -> do
    typ' <- Core.pis vs Builtin.Type
    runUnify (unify [] typ' typ) report

    let
      pvs = Vector.zipWith (\p v -> (p, pure v)) (telePlics ps) vs

    (cs', sizes) <- fmap unzip $ forM cs $ \(ConstrDef c t) ->
      checkConstrDef (ConstrDef c $ instantiateTele pure vs t) (pure var) pvs

    typeRep <- case b of
      Boxed -> Core.MkType <$> fetchPtrRep
      Unboxed -> do
        intRep <- fetchIntRep

        let tagRep = case cs of
              [] -> TypeRep.UnitRep
              [_] -> TypeRep.UnitRep
              _ -> intRep

        return
          $ productType (Core.MkType tagRep)
          $ foldl' sumType (Core.MkType TypeRep.UnitRep) sizes

    forM_ cs' $ \(ConstrDef qc e) ->
      logMeta "tc.data" ("checkDataDef res " ++ show qc) $ zonk e

    typeRep' <- whnfExpandingTypeReps typeRep
    logMeta "tc.data" "checkDataDef typeRep" $ zonk typeRep'

    result <- dataDef b vs cs'
    paramTypeRep <- Core.lams vs typeRep'
    return (result, paramTypeRep)

checkConstrDef
  :: ConstrDef PreM
  -> CoreM
  -> Vector (Plicitness, CoreM)
  -> Elaborate (ConstrDef CoreM, CoreM)
checkConstrDef (ConstrDef c ctype) typeCon typeArgs = do
  logPretty "tc.def.constr" "checkConstrDef constr" $ pure c
  ctype' <- checkPoly ctype Builtin.Type
  logMeta "tc.def.constr" "checkConstrDef ctype" $ zonk ctype'
  (ctype'', sizes) <- go ctype'
  let size = foldl' productType (Core.MkType TypeRep.UnitRep) sizes
  logMeta "tc.def.constr" "checkConstrDef size" $ zonk size
  return (ConstrDef c ctype'', size)
  where
    -- TODO: Check for escaping type variables and improve error message
    go t = do
      t' <- whnf t
      go' t'
    go' (Core.Pi h p t s) = do
      rep <- whnfExpandingTypeReps t
      Context.freshExtend (binding h p t) $ \v -> do
        (body, sizes) <- go $ instantiate1 (pure v) s
        body' <- Core.pi_ v body
        return (body', rep : sizes)
    go' typ@(Core.appsView -> (typeHead, typeArgs'))
      | Vector.length typeArgs == length typeArgs' = do
        runUnify (unify [] typeHead typeCon) report
        t <- constrainArgs (Core.apps typeCon typeArgs) (toList typeArgs) typeArgs'
        return (t, [])
      | otherwise = do
        runUnify (unify [] (Core.apps typeCon typeArgs) typ) report
        return (typ, [])

    constrainArgs returnType [] [] = return returnType
    constrainArgs returnType ((p1, arg1):args1) ((p2, arg2):args2)
      | p1 == p2 = do
        equal <- Equal.exec $ Equal.expr arg1 arg2
        if equal then
          constrainArgs returnType args1 args2
        else do
          typ <- typeOf arg1
          let
            returnType'
              = Core.Pi mempty Constraint (Builtin.Equals typ arg1 arg2)
              $ abstractNone returnType
          constrainArgs returnType' args1 args2
    constrainArgs _ _ _ =
      panic "constrainArgs mismatched lengths"


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
