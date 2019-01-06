module Elaboration.TypeCheck.Expr where

import Protolude

import Elaboration.Monad

checkPoly :: HasCallStack => PreM -> Polytype -> Elaborate CoreM
checkRho :: PreM -> Rhotype -> Elaborate CoreM
