module Elaboration.Constraint where

import Elaboration.Monad

whnf :: CoreM -> Infer CoreM
