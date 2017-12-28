module Inference.TypeCheck.Expr where

import Inference.Meta
import Inference.Monad

checkPoly :: ConcreteM -> Polytype -> Infer AbstractM
checkRho :: ConcreteM -> Rhotype -> Infer AbstractM
