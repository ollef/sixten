{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Syntax.Name where

import Data.String
import Data.Text(Text)
import Data.Hashable

import Util

newtype Name = Name (Hashed Text)
  deriving (Eq, Hashable, Ord, Show, IsString)

instance Semigroup Name where
  Name n1 <> Name n2 = Name $ hashed $ unhashed n1 <> unhashed n2

fromName :: IsString a => Name -> a
fromName (Name t) = fromText $ unhashed t

newtype Constr = Constr (Hashed Text)
  deriving (Eq, Hashable, Ord, Show, IsString)

fromConstr :: IsString a => Constr -> a
fromConstr (Constr t) = fromText $ unhashed t
