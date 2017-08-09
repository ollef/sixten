{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Syntax.Name where

import Data.String
import Data.Text(Text)
import Data.Hashable

import Util

newtype Name = Name Text
  deriving (Eq, Hashable, Ord, Show, IsString, Monoid)

fromName :: IsString a => Name -> a
fromName (Name t) = fromText t

newtype Constr = Constr Text
  deriving (Eq, Hashable, Ord, Show, IsString, Monoid)

fromConstr :: IsString a => Constr -> a
fromConstr (Constr t) = fromText t

constrToName :: Constr -> Name
constrToName (Constr c) = Name c

nameToConstr :: Name -> Constr
nameToConstr (Name n) = Constr n
