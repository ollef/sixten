module Syntax.NameHint where

import Data.Semigroup
import Data.String

import Syntax.Name

data NameHint
  = NoHint
  | NameHint !Name
  deriving Show

instance Semigroup NameHint where
  m@NameHint {} <> _ = m
  _ <> n@NameHint {} = n
  NoHint <> NoHint = NoHint

instance Monoid NameHint where
  mempty = NoHint
  mappend = (<>)

instance Eq NameHint where
  _ == _ = True

instance Ord NameHint where
  compare _ _ = EQ

instance IsString NameHint where
  fromString = NameHint . fromString

fromNameHint :: a -> (Name -> a) -> NameHint -> a
fromNameHint def _ NoHint = def
fromNameHint _ f (NameHint name) = f name
