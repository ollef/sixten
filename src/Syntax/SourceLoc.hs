module Syntax.SourceLoc(delta, render, SourceLoc, Span) where

import Text.Trifecta.Rendering(Rendering, render, Span(..))
import Text.Trifecta.Delta(delta)

type SourceLoc = Rendering
