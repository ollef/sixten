{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Syntax.ModuleHeader where

import Protolude hiding (moduleName)

import Data.HashSet(HashSet)

import Syntax.Name
import Syntax.QName
import Util.TopoSort

data ModuleHeader = ModuleHeader
  { moduleName :: !ModuleName
  , moduleExposedNames :: ExposedNames
  , moduleImports :: [Import]
  } deriving (Eq, Show, Generic, Hashable)

data ExposedNames
  = Exposed (HashSet Name) -- TODO allow qualified names
  | AllExposed
  deriving (Eq, Show, Generic, Hashable)

noneExposed :: ExposedNames
noneExposed = Exposed mempty

data Import = Import
  { importModule :: !ModuleName
  , importAlias :: !ModuleName
  , importExposedNames :: !ExposedNames
  } deriving (Eq, Show, Generic, Hashable)

moduleDependencyOrder
  :: Foldable t
  => t (x, ModuleHeader)
  -> [SCC (x, ModuleHeader)]
moduleDependencyOrder = topoSortWith (moduleName . snd) $ fmap importModule . moduleImports . snd
