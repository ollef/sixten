{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
module SourceLoc where

import Protolude hiding (TypeError)

import Text.Parsix.Highlight
import Text.Parsix.Position

import Pretty
import Syntax.QName
import Util

data SourceLoc
  = Absolute !AbsoluteSourceLoc
  | Relative !RelativeSourceLoc
  deriving (Eq, Ord, Show, Generic, Hashable)

noSourceLoc :: FilePath -> SourceLoc
noSourceLoc fp = Absolute $ AbsoluteSourceLoc
  { absoluteFile = fp
  , absoluteSpan = Span mempty mempty
  , absoluteHighlights = Nothing
  }

data AbsoluteSourceLoc = AbsoluteSourceLoc
  { absoluteFile :: FilePath
  , absoluteSpan :: !Span
  , absoluteHighlights :: !(Maybe Highlights)
  } deriving (Eq, Ord, Show, Generic, Hashable)

data RelativeSourceLoc = RelativeSourceLoc
  { relativeTo :: !QName
  , relativeSpan :: !Span
  } deriving (Eq, Ord, Show, Generic, Hashable)

spanRelativeTo :: Position -> Span -> Span
spanRelativeTo p (Span start end) = Span
  { spanStart = positionRelativeTo p start
  , spanEnd = positionRelativeTo p end
  }

positionRelativeTo :: Position -> Position -> Position
positionRelativeTo p1 p2 = Position
  { codeUnits = codeUnits p2 - codeUnits p1
  , visualRow = visualRow p2 - visualRow p1
  , visualColumn =
    if visualRow p1 == visualRow p2 then
      visualColumn p2 - visualColumn p1
    else
      visualColumn p2
  }

-- | Gives a summary (fileName:row:column) of the location
instance Pretty AbsoluteSourceLoc where
  pretty src
    = pretty (absoluteFile src)
    <> ":" <>
    if spanStart span == spanEnd span then
      shower startRow <> ":" <> shower startCol
    else if startRow == endRow then
      shower startRow <> ":" <> shower startCol <> "-" <> shower endCol
    else
      shower startRow <> ":" <> shower startCol <> "-" <> shower endRow <> ":" <> shower endCol
    where
      span = absoluteSpan src
      startRow = visualRow (spanStart span) + 1
      endRow = visualRow (spanEnd span) + 1
      startCol = visualColumn (spanStart span) + 1
      endCol = visualColumn (spanEnd span) + 1
