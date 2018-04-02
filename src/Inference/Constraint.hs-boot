module Inference.Constraint where

import Inference.Monad

whnf :: AbstractM -> Infer AbstractM
