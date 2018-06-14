module Inference.TypeCheck.Data where

import Control.Monad.Except
import Data.Foldable as Foldable

import {-# SOURCE #-} Inference.TypeCheck.Expr
import qualified Builtin.Names as Builtin
import Inference.Constraint as Constraint
import Inference.MetaVar
import Inference.MetaVar.Zonk
import Inference.Monad
import Inference.TypeOf
import Inference.Unify
import MonadContext
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Concrete.Scoped as Concrete
import TypedFreeVar
import qualified TypeRep
import VIX

checkConstrDef
  :: ConstrDef ConcreteM
  -> Infer (ConstrDef CoreM, CoreM, CoreM)
checkConstrDef (ConstrDef c typ) = do
  typ' <- zonk =<< checkPoly typ Builtin.Type
  (sizes, ret) <- go typ'
  let size = foldl' productType (Core.MkType TypeRep.UnitRep) sizes
  return (ConstrDef c typ', ret, size)
  where
    go :: CoreM -> Infer ([CoreM], CoreM)
    -- TODO: Check for escaping type variables?
    go (Core.Pi h p t s) = do
      v <- forall h p t
      (sizes, ret) <- go $ instantiate1 (pure v) s
      return (t : sizes, ret)
    go ret = return ([], ret)

checkDataType
  :: FreeV
  -> DataDef Concrete.Expr FreeV
  -> CoreM
  -> Infer (Definition (Core.Expr MetaVar) FreeV, CoreM)
checkDataType name (DataDef cs) typ = do
  typ' <- zonk typ
  logMeta 20 "checkDataType t" typ'

  vs <- forTeleWithPrefixM (Core.telescope typ') $ \h p s vs -> do
    let is = instantiateTele pure vs s
    forall h p is

  let constrRetType = Core.apps (pure name) $ (\v -> (varData v, pure v)) <$> vs
      abstr = teleAbstraction vs

  withVars vs $ do
    (cs', rets, sizes) <- fmap unzip3 $ forM cs $ \(ConstrDef c t) ->
      checkConstrDef $ ConstrDef c $ instantiateTele pure vs t

    mapM_ (unify [] constrRetType) rets

    intRep <- getIntRep

    let tagRep = case cs of
          [] -> TypeRep.UnitRep
          [_] -> TypeRep.UnitRep
          _ -> intRep

        typeRep
          = productType (Core.MkType tagRep)
          $ foldl' sumType (Core.MkType TypeRep.UnitRep) sizes

    unify [] Builtin.Type =<< typeOf constrRetType

    abstractedCs <- forM cs' $ \c@(ConstrDef qc e) -> do
      logMeta 20 ("checkDataType res " ++ show qc) e
      return $ abstract abstr <$> c

    let params = varTelescope vs
        typ'' = Core.pis params $ Scope Builtin.Type

    typeRep' <- whnfExpandingTypeReps typeRep
    let abstractedTypeRep = abstract abstr typeRep'
    logMeta 20 "checkDataType typeRep" typeRep'

    return (DataDefinition (DataDef abstractedCs) $ Core.lams params abstractedTypeRep, typ'')

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
