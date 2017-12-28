module Inference.TypeCheck.Data where

import Control.Monad.Except
import Data.Bifunctor
import Data.Foldable as Foldable

import qualified Builtin.Names as Builtin
import Inference.Class as Class
import Inference.Monad
import {-# SOURCE #-} Inference.TypeCheck.Expr
import Inference.TypeOf
import Inference.Unify
import Inference.Meta
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete.Scoped as Concrete
import qualified TypeRep
import VIX

checkConstrDef
  :: ConstrDef ConcreteM
  -> Infer (ConstrDef AbstractM, AbstractM, AbstractM)
checkConstrDef (ConstrDef c typ) = do
  typ' <- zonk =<< checkPoly typ Builtin.Type
  (sizes, ret) <- go typ'
  let size = foldl' productType (Abstract.MkType TypeRep.UnitRep) sizes
  return (ConstrDef c typ', ret, size)
  where
    go :: AbstractM -> Infer ([AbstractM], AbstractM)
    go (Abstract.Pi h p t s) = do
      v <- forall h p t
      (sizes, ret) <- go $ instantiate1 (pure v) s
      return (t : sizes, ret)
    go ret = return ([], ret)

checkDataType
  :: MetaA
  -> DataDef Concrete.Expr MetaA
  -> AbstractM
  -> Infer (Definition Abstract.Expr MetaA, AbstractM)
checkDataType name (DataDef cs) typ = do
  typ' <- zonk typ
  logMeta 20 "checkDataType t" typ'

  ps' <- forTeleWithPrefixM (Abstract.telescope typ') $ \h p s ps' -> do
    let is = instantiateTele pure (snd <$> ps') s
    v <- forall h p is
    return (p, v)

  let vs = snd <$> ps'
      constrRetType = Abstract.apps (pure name) $ second pure <$> ps'
      abstr = teleAbstraction vs

  (cs', rets, sizes) <- fmap unzip3 $ forM cs $ \(ConstrDef c t) ->
    checkConstrDef $ ConstrDef c $ instantiateTele pure vs t

  mapM_ (unify [] constrRetType) rets

  intRep <- getIntRep

  let tagRep = case cs of
        [] -> TypeRep.UnitRep
        [_] -> TypeRep.UnitRep
        _ -> intRep

      typeRep
        = productType (Abstract.MkType tagRep)
        $ foldl' sumType (Abstract.MkType TypeRep.UnitRep) sizes

  unify [] Builtin.Type =<< typeOfM constrRetType

  abstractedCs <- forM cs' $ \c@(ConstrDef qc e) -> do
    logMeta 20 ("checkDataType res " ++ show qc) e
    traverse (abstractM abstr) c

  params <- metaTelescopeM ps'
  let typ'' = Abstract.pis params $ Scope Builtin.Type

  typeRep' <- whnfExpandingTypeReps typeRep
  abstractedTypeRep <- abstractM abstr typeRep'
  logMeta 20 "checkDataType typeRep" typeRep'

  return (DataDefinition (DataDef abstractedCs) $ Abstract.lams params abstractedTypeRep, typ'')

-------------------------------------------------------------------------------
-- Type helpers
productType :: Abstract.Expr v -> Abstract.Expr v -> Abstract.Expr v
productType (Abstract.MkType TypeRep.UnitRep) e = e
productType e (Abstract.MkType TypeRep.UnitRep) = e
productType (Abstract.MkType a) (Abstract.MkType b) = Abstract.MkType $ TypeRep.product a b
productType a b = Builtin.ProductTypeRep a b

sumType :: Abstract.Expr v -> Abstract.Expr v -> Abstract.Expr v
sumType (Abstract.MkType TypeRep.UnitRep) e = e
sumType e (Abstract.MkType TypeRep.UnitRep) = e
sumType (Abstract.MkType a) (Abstract.MkType b) = Abstract.MkType $ TypeRep.sum a b
sumType a b = Builtin.SumTypeRep a b
