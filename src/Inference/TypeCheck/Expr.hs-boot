module Inference.TypeCheck.Expr where

import Inference.Monad

checkPoly :: ConcreteM -> Polytype -> Infer AbstractM
checkRho :: ConcreteM -> Rhotype -> Infer AbstractM
