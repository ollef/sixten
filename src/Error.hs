{-# LANGUAGE DefaultSignatures, GADTs, OverloadedStrings, PatternSynonyms #-}
module Error where

import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Trans.Identity
import Control.Monad.Writer
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

-- | Gives a summary (fileName:row:column) of the location
instance Pretty SourceLoc where
  pretty src
    = pretty (sourceLocFile src)
    <> ":" <> shower (visualRow loc + 1)
    <> ":" <> shower (visualColumn loc + 1)
    where
      loc = spanStart $ sourceLocSpan src

-- TODO handle spans and not just the start position
locationRendering :: SourceLoc -> Doc
locationRendering src = prettyPosition
  defaultStyle
  (spanStart $ sourceLocSpan src)
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

-------------------------------------------------------------------------------
-- Report class
class Monad m => MonadReport m where
  report :: Error -> m ()

  default report
    :: (MonadTrans t, MonadReport m1, m ~ t m1)
    => Error
    -> m ()
  report = lift . report

-------------------------------------------------------------------------------
-- mtl instances
-------------------------------------------------------------------------------
instance MonadReport m => MonadReport (ReaderT r m)
instance (Monoid w, MonadReport m) => MonadReport (WriterT w m)
instance MonadReport m => MonadReport (StateT s m)
instance MonadReport m => MonadReport (IdentityT m)
instance (Monoid w, MonadReport m) => MonadReport (RWST r w s m)
