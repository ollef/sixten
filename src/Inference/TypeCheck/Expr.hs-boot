module Inference.TypeCheck.Expr where

import Inference.Monad

checkPoly :: PreM -> Polytype -> Infer CoreM
checkRho :: PreM -> Rhotype -> Infer CoreM
