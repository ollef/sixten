{-# LANGUAGE DeriveGeneric, GeneralizedNewtypeDeriving, OverloadedStrings #-}
module Syntax.QName where

import Protolude

import Data.Foldable(toList)
import Data.List(intersperse, intercalate)
import Data.List.Split
import Data.String
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import GHC.Generics(Generic)

import Pretty
import Syntax.Name
import Util

data QName = QName !ModuleName !Name
  deriving (Eq, Generic, Ord, Show)

qnameModule :: QName -> ModuleName
qnameModule (QName m _) = m

qnameName :: QName -> Name
qnameName (QName _ n) = n

fromQName :: IsString a => QName -> a
fromQName (QName (ModuleName parts) name)
  = fromString
  $ intercalate "."
  $ toList
  $ fromName <$> parts <> pure name

unqualified :: Name -> QName
unqualified = QName (ModuleName mempty)

isUnqualified :: QName -> Maybe Name
isUnqualified (QName (ModuleName vs) n)
  | Vector.null vs = Just n
  | otherwise = Nothing

data QConstr = QConstr !QName !Constr
  deriving (Eq, Generic, Ord, Show)

qconstrConstr :: QConstr -> Constr
qconstrConstr (QConstr _ c) = c

qconstrTypeName :: QConstr -> QName
qconstrTypeName (QConstr n _) = n

fromQConstr :: (IsString a, Semigroup a) => QConstr -> a
fromQConstr (QConstr name constr) = fromQName name <> "." <> fromConstr constr

newtype ModuleName
  = ModuleName (Vector Name)
  deriving (Eq, Ord, Show, Semigroup, Monoid)

fromModuleName :: IsString a => ModuleName -> a
fromModuleName (ModuleName parts)
  = fromString
  $ intercalate "."
  $ toList
  $ fromName <$> parts

------------------------------------------------------------------------------
-- Instances
instance Hashable QName
instance Hashable QConstr
instance Hashable ModuleName where
  hashWithSalt s (ModuleName xs) = hashWithSalt s $ toList xs

instance IsString QName where
  fromString s = case unsnoc $ splitOn "." s of
    Nothing -> QName "" ""
    Just (ms, n) -> QName (ModuleName $ toVector $ fromString <$> ms) (fromString n)

instance IsString QConstr where
  fromString s = case unsnoc $ splitOn "." s of
    Nothing -> QConstr "" ""
    Just (ms, c) -> QConstr (fromString $ intercalate "." ms) (fromString c)

instance IsString ModuleName where
  fromString s = ModuleName $ toVector $ fromString <$> splitOn "." s

instance Pretty QName where
  prettyM (QName q n) | q == mempty = prettyM n
  prettyM (QName q n) = prettyM q <> "." <> prettyM n
instance Pretty QConstr where
  prettyM (QConstr q n) = prettyM q <> "." <> prettyM n
instance Pretty ModuleName where
  prettyM (ModuleName parts) = hcat $ intersperse "." (prettyM <$> toList parts)
