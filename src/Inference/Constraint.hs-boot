module Inference.Constraint where

import Inference.Monad

whnf :: CoreM -> Infer CoreM
