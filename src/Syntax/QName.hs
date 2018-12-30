{-# LANGUAGE DeriveGeneric, GeneralizedNewtypeDeriving, OverloadedStrings #-}
module Syntax.QName where

import Protolude

import Data.Foldable(toList)
import Data.List(intersperse, intercalate)
import Data.List.Split
import Data.String
import Data.Vector(Vector)
import GHC.Generics(Generic)

import Pretty
import Syntax.Name
import Util

-- | A qualified name.
data QName = QName !ModuleName !Name
  deriving (Eq, Generic, Ord, Show)

qnameModule :: QName -> ModuleName
qnameModule (QName m _) = m

qnameName :: QName -> Name
qnameName (QName _ n) = n

qnameParts :: QName -> Vector Name
qnameParts (QName (ModuleName ms) n) = ms <> pure n

fromQName :: IsString a => QName -> a
fromQName (QName (ModuleName parts) name)
  = fromString
  $ intercalate "."
  $ toList
  $ fromName <$> parts <> pure name

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

-- | A qualified name plus possibly a generated part, e.g. from lambda lifting
-- or closure conversion.
data GName = GName !QName !(Vector Name)
  deriving (Eq, Generic, Ord, Show)

gname :: QName -> GName
gname qn = GName qn mempty

gnameBaseName :: GName -> QName
gnameBaseName (GName qn _) = qn

gnameModule :: GName -> ModuleName
gnameModule (GName qn _) = qnameModule qn

gnameParts :: GName -> Vector Name
gnameParts (GName qn gns) = qnameParts qn <> gns

fromGName :: IsString a => GName -> a
fromGName (GName (QName (ModuleName parts) name) genNames)
  = fromString
  $ intercalate "."
  $ toList
  $ fromName <$> parts <> pure name <> genNames

------------------------------------------------------------------------------
-- Instances
instance Hashable QName
instance Hashable QConstr
instance Hashable GName where
  hashWithSalt s (GName qn xs) = s `hashWithSalt` qn `hashWithSalt` toList xs
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
instance Pretty GName where
  prettyM (GName qn gn) | gn == mempty = prettyM qn
  prettyM (GName qn gn) = prettyM qn <> "." <> hcat (intersperse "." (prettyM <$> toList gn))
instance Pretty ModuleName where
  prettyM (ModuleName parts) = hcat $ intersperse "." (prettyM <$> toList parts)
