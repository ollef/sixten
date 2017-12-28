module Inference.Constraint where

import Inference.Meta
import Inference.Monad

whnf :: AbstractM -> Infer AbstractM
