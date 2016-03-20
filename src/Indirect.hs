module Indirect where

import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Abstract as Constant

import Meta
type ConstantM = ConstantSize.Expr (MetaVar ConstantSize.Expr s)

inferType :: AbstractM s -> TCM s (ConstantM s, ConstantM s)
inferType expr = case expr of
  Abstract.Var v -> return (Constant.Var v, metaType v)
  Abstract.Global v -> undefined
  Con qc -> undefined
  Lit l -> undefined
  Pi h a t s -> undefined
  Lam h a t s -> undefined
  App e1 a e2 -> undefined
  Case e brs -> undefined
