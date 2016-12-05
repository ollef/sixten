module Syntax.SourceLoc(addSpan, delta, emptySpan, render, SourceLoc, Span) where

import Text.Trifecta.Rendering(Rendering, render, Span(..))
import Text.Trifecta.Delta(delta)

type SourceLoc = Rendering

emptySpan :: Span
emptySpan = Span mempty mempty mempty

addSpan :: Span -> Span -> Span
addSpan s1 s2 | s1 == emptySpan = s2
addSpan s1 s2 | s2 == emptySpan = s1
addSpan (Span s1 e1 b) (Span s2 e2 _) = Span (min s1 s2) (max e1 e2) b
