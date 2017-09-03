{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveGeneric, DeriveTraversable, GeneralizedNewtypeDeriving, OverloadedStrings #-}
module Syntax.Module where

import Data.Bifunctor
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
import Util.TopoSort

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

fromQConstr :: (IsString a, Monoid a) => QConstr -> a
fromQConstr (QConstr name constr) = fromQName name <> "." <> fromConstr constr

newtype ModuleName
  = ModuleName (Vector Name)
  deriving (Eq, Ord, Show, Monoid)

data Module contents = Module
  { moduleName :: !ModuleName
  , moduleExposedNames :: ExposedNames
  , moduleImports :: [Import]
  , moduleContents :: contents
  } deriving (Eq, Show, Functor, Foldable, Traversable)

fromModuleName :: IsString a => ModuleName -> a
fromModuleName (ModuleName parts)
  = fromString
  $ intercalate "."
  $ toList
  $ fromName <$> parts

data ExposedNames
  = Exposed (HashSet Name) -- TODO allow qualified names
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
  prettyM (QName q n) | q == mempty = prettyM n
  prettyM (QName q n) = prettyM q <> "." <> prettyM n
instance Pretty QConstr where
  prettyM (QConstr q n) = prettyM q <> "." <> prettyM n
instance Pretty ModuleName where
  prettyM (ModuleName parts) = hcat $ intersperse "." (prettyM <$> toList parts)

instance Monoid ExposedNames where
  mempty = Exposed mempty
  mappend AllExposed _ = AllExposed
  mappend _ AllExposed = AllExposed
  mappend (Exposed xs) (Exposed ys) = Exposed $ xs `mappend` ys

------------------------------------------------------------------------------
-- Imports
importedAliases
  :: MultiHashMap ModuleName (Either QConstr QName)
  -> Import
  -> MultiHashMap QName (Either QConstr QName)
importedAliases modules (Import modName asName exposed) =
  as unqualified expNames `multiUnion` as (QName asName) modContents
  where
    modContents :: MultiHashMap Name (Either QConstr QName)
    modContents = multiFromList
      $ either
        (\c -> (fromConstr $ qconstrConstr c, Left c))
        (\d -> (qnameName d, Right d))
      <$> HashSet.toList names
      where
        -- TODO error if import missing
        names = HashMap.lookupDefault (error $ "Can't find " <> show modName) modName modules

    expNames :: MultiHashMap Name (Either QConstr QName)
    expNames = case exposed of
      AllExposed -> modContents
      Exposed names -> HashMap.intersection modContents (HashSet.toMap names)

    as
      :: (Eq b, Hashable b)
      => (a -> b)
      -> MultiHashMap a (Either QConstr QName)
      -> MultiHashMap b (Either QConstr QName)
    as f = HashMap.fromList .  fmap (first f) . HashMap.toList

dependencyOrder
  :: (Foldable t, Functor t)
  => t (Module contents)
  -> [[Module contents]]
dependencyOrder = topoSortWith moduleName $ fmap importModule . moduleImports
