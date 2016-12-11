{-# LANGUAGE DeriveGeneric, GeneralizedNewtypeDeriving #-}
module Syntax.Name where

import GHC.Generics(Generic)
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

constrToName :: Constr -> Name
constrToName (Constr c) = Name c

nameToConstr :: Name -> Constr
nameToConstr (Name n) = Constr n

data QConstr = QConstr !Name !Constr
  deriving (Eq, Generic, Ord, Show)

instance Hashable QConstr

-- TODO remove?
qualify :: Name -> Either Constr QConstr -> QConstr
qualify n (Right qc@(QConstr n' _)) | n == n' = qc
qualify n (Left c) = QConstr n c
qualify n e = error $ "qualify " ++ show (n, e)
