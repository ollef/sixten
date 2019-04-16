{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Error where

import Protolude hiding (TypeError)

import Pretty
import SourceLoc

data ErrorKind
  = SyntaxErrorKind
  | TypeErrorKind
  | CommandLineErrorKind
  | InternalErrorKind
  deriving (Eq, Show, Generic, Hashable)

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

-- TODO remove
instance Hashable Error where
  hashWithSalt s (Error k _ l _) = s `hashWithSalt` k `hashWithSalt` l

instance Eq Error where
  Error k1 _ l1 _ == Error k2 _ l2 _ = k1 == k2 && l1 == l2

{-# COMPLETE SyntaxError, TypeError, CommandLineError, InternalError #-}
pattern SyntaxError :: Doc -> Maybe SourceLoc -> Doc -> Error
pattern SyntaxError s l f = Error SyntaxErrorKind s l f

pattern TypeError :: Doc -> Maybe SourceLoc -> Doc -> Error
pattern TypeError s l f = Error TypeErrorKind s l f

pattern CommandLineError :: Doc -> Maybe SourceLoc -> Doc -> Error
pattern CommandLineError s l f = Error CommandLineErrorKind s l f

pattern InternalError :: Doc -> Maybe SourceLoc -> Doc -> Error
pattern InternalError s l f = Error InternalErrorKind s l f
