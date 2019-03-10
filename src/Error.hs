{-# LANGUAGE GADTs, OverloadedStrings, PatternSynonyms #-}
module Error where

import Protolude hiding (TypeError)

import Data.Text(Text)
import Data.Text.Prettyprint.Doc(line)
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Text.Prettyprint.Doc.Render.Terminal
import Text.Parsix.Highlight
import Text.Parsix.Position

import Pretty
import Util

data SourceLoc = SourceLocation
  { sourceLocFile :: FilePath
  , sourceLocSpan :: !Span
  , sourceLocSource :: Text
  , sourceLocHighlights :: Highlights
  } deriving (Eq, Ord, Show)

noSourceLoc :: FilePath -> SourceLoc
noSourceLoc fp = SourceLocation
  { sourceLocFile = "<no source location (" ++ fp ++ ")>"
  , sourceLocSpan = Span (Position 0 0 0) (Position 0 0 0)
  , sourceLocSource = mempty
  , sourceLocHighlights = mempty
  }

-- | Gives a summary (fileName:row:column) of the location
instance Pretty SourceLoc where
  pretty src
    = pretty (sourceLocFile src)
    <> ":" <>
    if spanStart span == spanEnd span then
      shower startRow <> ":" <> shower startCol
    else if startRow == endRow then
      shower startRow <> ":" <> shower startCol <> "-" <> shower endCol
    else
      shower startRow <> ":" <> shower startCol <> "-" <> shower endRow <> ":" <> shower endCol
    where
      span = sourceLocSpan src
      startRow = visualRow (spanStart span) + 1
      endRow = visualRow (spanEnd span) + 1
      startCol = visualColumn (spanStart span) + 1
      endCol = visualColumn (spanEnd span) + 1

-- TODO handle spans and not just the start position
locationRendering :: SourceLoc -> Doc
locationRendering src = prettySpan
  defaultStyle
  (sourceLocSpan src)
  (sourceLocSource src)
  (sourceLocHighlights src)

data ErrorKind
  = SyntaxErrorKind
  | TypeErrorKind
  | CommandLineErrorKind
  | InternalErrorKind
  deriving Show

instance Pretty ErrorKind where
  pretty SyntaxErrorKind = "Syntax error"
  pretty TypeErrorKind = "Type error"
  pretty CommandLineErrorKind = "Command-line error"
  pretty InternalErrorKind = "Internal compiler error"

data Error = Error
  { errorKind :: !ErrorKind
  , errorSummary :: !Doc
  , errorLocation :: !(Maybe SourceLoc)
  , errorFootnote :: !Doc
  } deriving Show

{-# COMPLETE SyntaxError, TypeError, CommandLineError, InternalError #-}
pattern SyntaxError :: Doc -> Maybe SourceLoc -> Doc -> Error
pattern SyntaxError s l f = Error SyntaxErrorKind s l f

pattern TypeError :: Doc -> Maybe SourceLoc -> Doc -> Error
pattern TypeError s l f = Error TypeErrorKind s l f

pattern CommandLineError :: Doc -> Maybe SourceLoc -> Doc -> Error
pattern CommandLineError s l f = Error CommandLineErrorKind s l f

pattern InternalError :: Doc -> Maybe SourceLoc -> Doc -> Error
pattern InternalError s l f = Error InternalErrorKind s l f

instance Pretty Error where
  pretty (Error kind summary (Just loc) footnote)
    = pretty loc <> ":" PP.<+> red (pretty kind) <> ":" PP.<+> summary
    <> line <> locationRendering loc
    <> line <> footnote
    <> line
  pretty (Error kind summary Nothing footnote)
    = red (pretty kind) <> ":" <> summary
    <> line <> footnote
    <> line

printError :: Error -> IO ()
printError = putDoc . pretty

data ErrorException = ErrorException
  deriving Show

instance Exception ErrorException where
