{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
module Driver.Query (module Rock, module Driver.Query) where

import Protolude hiding (TypeRep)

import Data.HashMap.Lazy(HashMap)
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Rock
import Util.MultiHashMap(MultiHashMap)
import qualified Util.MultiHashMap as MultiHashMap

import qualified Backend.Generate.Submodule as Generate
import Backend.Target as Target
import Command.Compile.Options as Compile
import Data.GADT.Compare.Deriving
import Error
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Pre.Definition as Pre
import qualified Syntax.Pre.Scoped as Pre
import qualified Syntax.Pre.Unscoped as Unscoped
import qualified Syntax.Sized.Definition as Sized
import qualified Syntax.Sized.Extracted as Extracted
import qualified Syntax.Sized.Lifted as Lifted
import TypeRep

type BindingGroup = HashSet QName
type ModuleDefinitions = HashMap QName (SourceLoc, Unscoped.TopLevelDefinition)
type ResolvedModule = [ResolvedBindingGroup]
type ResolvedBindingGroup = [(QName, SourceLoc, Closed (Pre.Definition Pre.Expr))]
type ElaboratedDef = (SourceLoc, ClosedDefinition Core.Expr, Biclosed Core.Expr)
type ElaboratedGroup = HashMap GName ElaboratedDef

data Query a where
  Files :: Query [FilePath]
  File :: FilePath -> Query Text
  Target :: Query Target
  Builtins :: Query (HashMap QName ElaboratedDef)
  ParsedModule :: FilePath -> Query (ModuleHeader, [(SourceLoc, Unscoped.TopLevelDefinition)])
  ModuleHeaders :: Query (HashMap FilePath ModuleHeader)
  ModuleFiles :: Query (HashMap ModuleName FilePath)
  ModuleFile :: ModuleName -> Query (Maybe FilePath)
  DupCheckedModule :: ModuleName -> Query (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition))
  ModuleExports :: ModuleName -> Query (HashSet QName, HashSet QConstr)
  ResolvedModule :: ModuleName -> Query ResolvedModule
  ResolvedBindingGroups :: ModuleName -> Query (HashMap BindingGroup ResolvedBindingGroup)
  BindingGroupMap :: ModuleName -> Query (HashMap QName BindingGroup)
  BindingGroup :: QName -> Query BindingGroup
  ElaboratedGroup :: BindingGroup -> Query ElaboratedGroup
  SimplifiedGroup :: BindingGroup -> Query ElaboratedGroup

  Type :: GName -> Query (Biclosed Core.Expr)
  Definition :: GName -> Query (ClosedDefinition Core.Expr)
  QConstructor :: QConstr -> Query (Int, Biclosed Core.Expr)
  -- TODO should perhaps be derived?
  ClassMethods :: QName -> Query (Maybe [(Name, SourceLoc)])
  Instances :: ModuleName -> Query (MultiHashMap QName QName)

  ConstrIndex :: QConstr -> Query (Maybe Integer)

  LambdaLifted :: BindingGroup -> Query [(GName, Closed (Sized.Definition Lifted.Expr))]
  RuntimeDefinitions :: Query (HashMap QName (Closed (Sized.Definition Lifted.Expr)))
  ConvertedSignatures :: BindingGroup -> Query (HashMap GName (Maybe Lifted.FunSignature, [(GName, Closed (Sized.Definition Lifted.Expr))]))
  ConvertedSignature :: GName -> Query (Maybe Lifted.FunSignature)
  Converted :: BindingGroup -> Query [(GName, Closed (Sized.Definition Lifted.Expr))]
  DirectionSignatures :: BindingGroup -> Query (HashMap GName (Closed (Sized.Definition Lifted.Expr), Signature ReturnIndirect))
  DirectionSignature :: GName -> Query (Maybe (Signature ReturnIndirect))
  ExtractedSubmodules :: BindingGroup -> Query [(GName, Extracted.Submodule (Closed (Sized.Definition Extracted.Expr)))]
  GeneratedSubmodules :: BindingGroup -> Query [Generate.Submodule]

  CheckAll :: Query [ElaboratedGroup]
  CompileAll :: FilePath -> Compile.Options -> Query ()

deriving instance Show (Query a)

deriveGEq ''Query
deriveGCompare ''Query

-- Derived queries
fetchModuleHeader :: MonadFetch Query m => FilePath -> m ModuleHeader
fetchModuleHeader file = fst <$> fetch (ParsedModule file)

fetchDefinition :: MonadFetch Query m => GName -> m (Definition (Core.Expr meta) v)
fetchDefinition name = openDefinition <$> fetch (Definition name)

fetchType :: MonadFetch Query m => GName -> m (Core.Type meta v)
fetchType name = biopen <$> fetch (Type name)

fetchInstances :: MonadFetch Query m => QName -> ModuleName -> m (HashSet QName)
fetchInstances className moduleName_ = do
  classInstances <- fetch $ Instances moduleName_
  return $ MultiHashMap.lookup className classInstances

fetchQConstructor :: MonadFetch Query m => QConstr -> m (Int, Core.Type meta v)
fetchQConstructor qc = second biopen <$> fetch (QConstructor qc)

fetchIntRep :: MonadFetch Query m => m TypeRep
fetchIntRep = TypeRep.intRep <$> fetch Driver.Query.Target

fetchTypeRep :: MonadFetch Query m => m TypeRep
fetchTypeRep = TypeRep.typeRep <$> fetch Driver.Query.Target

fetchPtrRep :: MonadFetch Query m => m TypeRep
fetchPtrRep = TypeRep.ptrRep <$> fetch Driver.Query.Target

fetchPiRep :: MonadFetch Query m => m TypeRep
fetchPiRep = TypeRep.piRep <$> fetch Driver.Query.Target

fetchModules :: MonadFetch Query m => m (HashSet ModuleName)
fetchModules = HashSet.fromMap . void <$> fetch ModuleFiles

fetchBindingGroups :: MonadFetch Query m => ModuleName -> m (HashSet BindingGroup)
fetchBindingGroups mname
  = HashSet.fromMap . void <$> fetch (ResolvedBindingGroups mname)
