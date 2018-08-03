module Elaboration.TypeCheck.Data where

import Control.Monad.Except
import Data.Foldable as Foldable

import qualified Builtin.Names as Builtin
import Elaboration.Constraint as Constraint
import Elaboration.MetaVar
import Elaboration.Monad
import Elaboration.TypeCheck.Expr
import Elaboration.TypeOf
import Elaboration.Unify
import MonadContext
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Pre.Scoped as Pre
import TypedFreeVar
import qualified TypeRep
import VIX

checkDataDef
  :: FreeV
  -> DataDef Pre.Expr FreeV
  -> Elaborate (DataDef (Core.Expr MetaVar) FreeV, CoreM)
checkDataDef var (DataDef ps cs) = do

  -- TODO: These vars are typechecked twice (in checkAndGeneraliseDefs as the
-- expected type and here). Can we clean this up?
  vs <- forTeleWithPrefixM ps $ \h p s vs -> do
    let t = instantiateTele pure vs s
    t' <- withVars vs $ checkPoly t Builtin.Type
    forall h p t'

  withVars vs $ do
    unify [] (Core.pis vs Builtin.Type) $ varType var

    let constrRetType = Core.apps (pure var) $ (\v -> (varData v, pure v)) <$> vs

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

    forM_ cs' $ \(ConstrDef qc e) ->
      logMeta 20 ("checkDataDef res " ++ show qc) e

    typeRep' <- whnfExpandingTypeReps typeRep
    logMeta 20 "checkDataDef typeRep" typeRep'

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
