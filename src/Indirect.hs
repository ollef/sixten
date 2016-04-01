module Indirect where

import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.ConstantSize as Constant
import TCM
import Meta hiding(AbstractM)

type ConstantM s = Constant.Expr (MetaVar Constant.Expr s)
type AbstractM s = Abstract.Expr (MetaVar Constant.Expr s)

inferType :: AbstractM s -> TCM s (ConstantM s, ConstantM s)
inferType expr = case expr of
  Abstract.Var v -> return (pure v, metaType v)
  Abstract.Global v -> do
    (_, typ) <- definition v
    return (Constant.Global v, typ)
  Abstract.Con qc -> do
    typ <- qconstructor qc
    return (Constant.Con qc, typ)
  Abstract.Lit l -> return (Constant.Lit l, Builtin.Size)
  Abstract.Pi h a t s -> do

  Abstract.Lam h a t s -> undefined
  Abstract.App e1 a e2 -> undefined
  Abstract.Case e brs -> undefined
