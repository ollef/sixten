{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Util.Orphans where

import Protolude

import Data.Bifunctor.Flip
import Data.Hashable.Lifted
import Data.IntervalMap.FingerTree(IntervalMap)
import Text.Parser.Token.Highlight
import Data.IntervalMap.FingerTree as IntervalMap
import Data.Vector(Vector)
import Data.Vector.Instances()
import qualified LLVM.AST as LLVM
import qualified LLVM.AST.AddrSpace as LLVM
import qualified LLVM.AST.CallingConvention as LLVM
import qualified LLVM.AST.COMDAT as LLVM
import qualified LLVM.AST.Constant as LLVM
import qualified LLVM.AST.DLL as LLVM
import qualified LLVM.AST.Float as LLVM
import qualified LLVM.AST.FloatingPointPredicate as LLVM
import qualified LLVM.AST.FunctionAttribute as LLVM
import qualified LLVM.AST.InlineAssembly as LLVM
import qualified LLVM.AST.IntegerPredicate as LLVM
import qualified LLVM.AST.Linkage as LLVM
import qualified LLVM.AST.Operand as LLVM
import qualified LLVM.AST.ParameterAttribute as LLVM
import qualified LLVM.AST.RMWOperation as LLVM
import qualified LLVM.AST.ThreadLocalStorage as LLVM
import qualified LLVM.AST.Visibility as LLVM
import Text.Parsix.Position

instance Hashable1 Vector where
  liftHashWithSalt f s = liftHashWithSalt f s . toList

instance Hashable Position where

instance Hashable Span where

deriving instance Generic Highlight
instance Hashable Highlight

instance Hashable1 NonEmpty where

instance Hashable (g b a) => Hashable (Flip g a b) where

instance Hashable a => Hashable (IntervalMap.Interval a) where
instance (Ord v, Hashable v, Hashable a) => Hashable (IntervalMap v a) where
  hashWithSalt s i = hashWithSalt s $ (`IntervalMap.intersections` i) <$> IntervalMap.bounds i

instance Hashable LLVM.AddrSpace where
instance Hashable LLVM.BasicBlock where
instance Hashable LLVM.BasicTypeTag where
instance Hashable LLVM.CallingConvention where
instance Hashable LLVM.ChecksumInfo where
instance Hashable LLVM.ChecksumKind where
instance Hashable LLVM.Constant where
instance Hashable LLVM.DIAccessibility where
instance Hashable LLVM.DIBasicType where
instance Hashable LLVM.DICompileUnit where
instance Hashable LLVM.DICompositeType where
instance Hashable LLVM.DICount where
instance Hashable LLVM.DIDerivedType where
instance Hashable LLVM.DIEnumerator where
instance Hashable LLVM.DIExpression where
instance Hashable LLVM.DIFile where
instance Hashable LLVM.DIFlag where
instance Hashable LLVM.DIGlobalVariable where
instance Hashable LLVM.DIGlobalVariableExpression where
instance Hashable LLVM.DIImportedEntity where
instance Hashable LLVM.DIInheritance where
instance Hashable LLVM.DILexicalBlockBase where
instance Hashable LLVM.DILocalScope where
instance Hashable LLVM.DILocalVariable where
instance Hashable LLVM.DILocation where
instance Hashable LLVM.DIMacroInfo where
instance Hashable LLVM.DIMacroNode where
instance Hashable LLVM.DIModule where
instance Hashable LLVM.DINamespace where
instance Hashable LLVM.DINode where
instance Hashable LLVM.DIObjCProperty where
instance Hashable LLVM.DIScope where
instance Hashable LLVM.DISubprogram where
instance Hashable LLVM.DISubrange where
instance Hashable LLVM.DISubroutineType where
instance Hashable LLVM.DITemplateParameter where
instance Hashable LLVM.DIType where
instance Hashable LLVM.DIVariable where
instance Hashable LLVM.DWOp where
instance Hashable LLVM.DWOpFragment where
instance Hashable LLVM.DebugEmissionKind where
instance Hashable LLVM.Definition where
instance Hashable LLVM.DerivedTypeTag where
instance Hashable LLVM.Dialect where
instance Hashable LLVM.Encoding where
instance Hashable LLVM.FastMathFlags where
instance Hashable LLVM.FloatingPointPredicate where
instance Hashable LLVM.FloatingPointType where
instance Hashable LLVM.FunctionAttribute where
instance Hashable LLVM.Global where
instance Hashable LLVM.GroupID where
instance Hashable LLVM.ImportedEntityTag where
instance Hashable LLVM.InlineAssembly where
instance Hashable LLVM.Instruction where
instance Hashable LLVM.IntegerPredicate where
instance Hashable LLVM.LandingPadClause where
instance Hashable LLVM.Linkage where
instance Hashable LLVM.MDNode where
instance Hashable LLVM.MemoryOrdering where
instance Hashable LLVM.Metadata where
instance Hashable LLVM.MetadataNodeID where
instance Hashable LLVM.Model where
instance Hashable LLVM.Name where
instance Hashable LLVM.Operand where
instance Hashable LLVM.Parameter where
instance Hashable LLVM.ParameterAttribute where
instance Hashable LLVM.RMWOperation where
instance Hashable LLVM.SelectionKind where
instance Hashable LLVM.SomeFloat where
instance Hashable LLVM.StorageClass where
instance Hashable LLVM.SynchronizationScope where
instance Hashable LLVM.TailCallKind where
instance Hashable LLVM.TemplateValueParameterTag where
instance Hashable LLVM.Terminator where
instance Hashable LLVM.Type where
instance Hashable LLVM.UnnamedAddr where
instance Hashable LLVM.Virtuality where
instance Hashable LLVM.Visibility where
instance Hashable a => Hashable (LLVM.MDRef a) where
instance Hashable a => Hashable (LLVM.Named a) where
