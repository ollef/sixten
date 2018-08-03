module Elaboration.TypeCheck.Expr where

import Elaboration.Monad

checkPoly :: PreM -> Polytype -> Infer CoreM
checkRho :: PreM -> Rhotype -> Infer CoreM
