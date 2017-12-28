module Inference.Class where

import Inference.Meta
import Inference.Monad

whnf :: AbstractM -> Infer AbstractM
