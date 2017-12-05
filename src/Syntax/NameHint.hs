module Syntax.NameHint where

import Data.String

import Syntax.Name

data NameHint
  = NoHint
  | NameHint !Name
  deriving Show

instance Monoid NameHint where
  mempty = NoHint
  m@NameHint {} `mappend` _ = m
  _ `mappend` n@NameHint {} = n
  NoHint `mappend` NoHint = NoHint

instance Eq NameHint where
  _ == _ = True

instance Ord NameHint where
  compare _ _ = EQ

instance IsString NameHint where
  fromString = NameHint . fromString

fromNameHint :: a -> (Name -> a) -> NameHint -> a
fromNameHint def _ NoHint = def
fromNameHint _ f (NameHint name) = f name
