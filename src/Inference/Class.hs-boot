module Inference.Class where

import Inference.Monad
import Meta

whnf :: AbstractM -> Infer AbstractM
