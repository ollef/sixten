{-# LANGUAGE FlexibleContexts #-}
module Elaboration.Constraint where

import Elaboration.Monad

whnf :: MonadElaborate m => CoreM -> m CoreM
