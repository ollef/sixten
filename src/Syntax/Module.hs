{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Syntax.Module where

import Protolude hiding (moduleName)

import Data.HashSet(HashSet)

import Syntax.Name
import Syntax.QName
import Util.TopoSort

data Module contents = Module
  { moduleName :: !ModuleName
  , moduleExposedNames :: ExposedNames
  , moduleImports :: [Import]
  , moduleContents :: contents
  } deriving (Eq, Show, Functor, Foldable, Traversable)

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
  => t (Module contents)
  -> [SCC (Module contents)]
moduleDependencyOrder = topoSortWith moduleName $ fmap importModule . moduleImports

------------------------------------------------------------------------------
-- Instances
instance Semigroup ExposedNames where
  AllExposed <> _ = AllExposed
  _ <> AllExposed = AllExposed
  Exposed xs <> Exposed ys = Exposed $ xs <> ys

instance Monoid ExposedNames where
  mempty = Exposed mempty
  mappend = (<>)
