{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Syntax.NameHint where

import Protolude

import Data.String

import Syntax.Name

data NameHint
  = NoHint
  | NameHint !Name
  deriving (Eq, Ord, Show, Generic, Hashable)

instance Semigroup NameHint where
  m@NameHint {} <> _ = m
  _ <> n@NameHint {} = n
  NoHint <> NoHint = NoHint

instance Monoid NameHint where
  mempty = NoHint
  mappend = (<>)

instance IsString NameHint where
  fromString = NameHint . fromString

fromNameHint :: a -> (Name -> a) -> NameHint -> a
fromNameHint def _ NoHint = def
fromNameHint _ f (NameHint name) = f name
