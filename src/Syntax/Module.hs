{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveGeneric, DeriveTraversable, OverloadedStrings #-}
module Syntax.Module where

import Data.Foldable(toList)
import Data.Hashable
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.List(intersperse, intercalate)
import Data.List.Split
import Data.Monoid
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

data QConstr = QConstr QName Constr
  deriving (Eq, Generic, Ord, Show)

qconstrConstr :: QConstr -> Constr
qconstrConstr (QConstr _ c) = c

qconstrTypeName :: QConstr -> QName
qconstrTypeName (QConstr n _) = n

newtype ModuleName
  = ModuleName (Vector Name)
  deriving (Eq, Ord, Show)

data Module contents = Module
  { moduleName :: !ModuleName
  , moduleExposedNames :: ExposedNames
  , moduleImports :: [Import]
  , moduleContents :: contents
  } deriving (Eq, Show, Functor, Foldable, Traversable)

data ExposedNames
  = Exposed (HashSet Name)
  | AllExposed
  deriving (Eq, Show)

data Import = Import
  { importModule :: !ModuleName
  , importAlias :: !ModuleName
  , importExposedNames :: !ExposedNames
  } deriving (Eq, Show)

------------------------------------------------------------------------------
-- Instances
instance Hashable QName
instance Hashable QConstr
instance Hashable ModuleName where
  hashWithSalt s (ModuleName xs) = hashWithSalt s $ toList xs

instance IsString QName where
  fromString s = case parts of
    [] -> QName "" ""
    _ -> QName
      (ModuleName $ toVector $ fromString <$> init parts)
      (fromString $ last parts)
    where
      parts = splitOn "." s

instance IsString QConstr where
  fromString s = case parts of
    [] -> QConstr "" ""
    _ -> QConstr
      (fromString $ intercalate "." $ init parts)
      (fromString $ last parts)
    where
      parts = splitOn "." s

instance IsString ModuleName where
  fromString s = ModuleName $ toVector $ fromString <$> parts
    where
      parts = splitOn "." s

instance Pretty QName where
  prettyM (QName q n) = prettyM q <> "." <> prettyM n
instance Pretty QConstr where
  prettyM (QConstr q n) = prettyM q <> "." <> prettyM n
instance Pretty ModuleName where
  prettyM (ModuleName parts) = hcat $ intersperse "," (prettyM <$> toList parts)

instance Monoid ExposedNames where
  mempty = Exposed mempty
  mappend AllExposed _ = AllExposed
  mappend _ AllExposed = AllExposed
  mappend (Exposed xs) (Exposed ys) = Exposed $ xs `mappend` ys

------------------------------------------------------------------------------
-- Imports
importedAliases
  :: MultiHashMap ModuleName Name
  -> Import
  -> MultiHashMap QName QName
importedAliases modules (Import modName asName exposed) =
  as unqualified expNames `multiUnion` as (QName asName) modContents
  where
    modContents = HashMap.lookupDefault (error $ "Can't find " <> show modName) modName modules -- TODO error if import missing

    expNames = case exposed of
      AllExposed -> modContents
      Exposed names -> names

    as f names = HashMap.fromList
      [ (f name, HashSet.singleton $ QName modName name)
      | name <- HashSet.toList names
      ]
