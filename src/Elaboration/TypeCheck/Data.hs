{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Elaboration.TypeCheck.Data where

import Prelude(unzip3)
import Protolude hiding (typeRep)

import qualified Builtin.Names as Builtin
import Driver.Query
import Effect
import Elaboration.Constraint as Constraint
import Elaboration.MetaVar
import Elaboration.MetaVar.Zonk
import Elaboration.Monad
import Elaboration.TypeCheck.Expr
import Elaboration.TypeOf
import Elaboration.Unify
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Pre.Scoped as Pre
import TypedFreeVar
import qualified TypeRep

checkDataDef
  :: FreeV
  -> DataDef Pre.Expr FreeV
  -> Elaborate (DataDef (Core.Expr MetaVar) FreeV, CoreM)
checkDataDef var (DataDef ps cs) =
  -- TODO: These vars are typechecked twice (in checkAndGeneraliseDefs as the
-- expected type and here). Can we clean this up?
  teleMapExtendContext ps (`checkPoly` Builtin.Type) $ \vs -> do
    runUnify (unify [] (Core.pis vs Builtin.Type) $ varType var) report

    let constrRetType = Core.apps (pure var) $ (\v -> (varData v, pure v)) <$> vs

    (cs', rets, sizes) <- fmap unzip3 $ forM cs $ \(ConstrDef c t) ->
      checkConstrDef $ ConstrDef c $ instantiateTele pure vs t

    mapM_ (flip runUnify report . unify [] constrRetType) rets

    intRep <- fetchIntRep

    let tagRep = case cs of
          [] -> TypeRep.UnitRep
          [_] -> TypeRep.UnitRep
          _ -> intRep

        typeRep
          = productType (Core.MkType tagRep)
          $ foldl' sumType (Core.MkType TypeRep.UnitRep) sizes

    flip runUnify report . unify [] Builtin.Type =<< typeOf constrRetType

    forM_ cs' $ \(ConstrDef qc e) ->
      logMeta "tc.data" ("checkDataDef res " ++ show qc) $ zonk e

    typeRep' <- whnfExpandingTypeReps typeRep
    logMeta "tc.data" "checkDataDef typeRep" $ zonk typeRep'

    return (dataDef vs cs', Core.lams vs typeRep')

checkConstrDef
  :: ConstrDef PreM
  -> Elaborate (ConstrDef CoreM, CoreM, CoreM)
checkConstrDef (ConstrDef c typ) = do
  typ' <- checkPoly typ Builtin.Type
  (sizes, ret) <- go typ'
  let size = foldl' productType (Core.MkType TypeRep.UnitRep) sizes
  return (ConstrDef c typ', ret, size)
  where
    -- TODO: Check for escaping type variables?
    go t = do
      t' <- whnf t
      go' t'
    go' (Core.Pi h p t s) = do
      v <- forall h p t
      (sizes, ret) <- go $ instantiate1 (pure v) s
      return (t : sizes, ret)
    go' ret = return ([], ret)

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
