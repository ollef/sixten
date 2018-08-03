module Elaboration.TypeCheck.Expr where

import Elaboration.Monad

checkPoly :: PreM -> Polytype -> Elaborate CoreM
checkRho :: PreM -> Rhotype -> Elaborate CoreM
