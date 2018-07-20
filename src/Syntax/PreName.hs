module Syntax.PreName where

import Control.Applicative
import Data.Hashable
import Data.Semigroup
import Data.String
import Data.Text(Text)

import Error
import Pretty
import Util

-- | An unresolved name
data PreName = PreName
  { preNameSourceLoc :: Maybe SourceLoc
  , preNameText :: !Text
  } deriving Show

instance Eq PreName where
  PreName _ t1 == PreName _ t2 = t1 == t2

instance Ord PreName where
  compare (PreName _ t1) (PreName _ t2) = compare t1 t2

instance Hashable PreName where
  hashWithSalt s (PreName _ t) = hashWithSalt s t

instance IsString PreName where
  fromString = PreName Nothing . fromString

instance Semigroup PreName where
  PreName loc1 t1 <> PreName loc2 t2 = PreName (loc1 <|> loc2) (t1 <> t2)

instance Monoid PreName where
  mempty = PreName Nothing mempty
  mappend = (<>)

fromPreName :: IsString a => PreName -> a
fromPreName (PreName _ t) = fromText t

instance Pretty PreName where pretty (PreName _ n) = pretty n
