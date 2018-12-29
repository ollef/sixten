module Elaboration.MetaVar.Zonk where

import Protolude

import Syntax.Core
import Elaboration.MetaVar

zonk :: MonadIO m => Expr MetaVar v -> m (Expr MetaVar v)
