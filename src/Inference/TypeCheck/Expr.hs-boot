module Inference.TypeCheck.Expr where

import Inference.Monad

checkPoly :: ConcreteM -> Polytype -> Infer CoreM
checkRho :: ConcreteM -> Rhotype -> Infer CoreM
