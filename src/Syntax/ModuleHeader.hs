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
  } deriving (Eq, Show)

data ExposedNames
  = Exposed (HashSet Name) -- TODO allow qualified names
  | AllExposed
  deriving (Eq, Show)

data Import = Import
  { importModule :: !ModuleName
  , importAlias :: !ModuleName
  , importExposedNames :: !ExposedNames
  } deriving (Eq, Show)

moduleDependencyOrder
  :: Foldable t
  => t (ModuleHeader, contents)
  -> [SCC (ModuleHeader, contents)]
moduleDependencyOrder = topoSortWith (moduleName . fst) $ fmap importModule . moduleImports . fst

------------------------------------------------------------------------------
-- Instances
instance Semigroup ExposedNames where
  AllExposed <> _ = AllExposed
  _ <> AllExposed = AllExposed
  Exposed xs <> Exposed ys = Exposed $ xs <> ys

instance Monoid ExposedNames where
  mempty = Exposed mempty
  mappend = (<>)
