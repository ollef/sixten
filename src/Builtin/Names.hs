{-# LANGUAGE OverloadedStrings, PatternSynonyms, ViewPatterns #-}
module Builtin.Names where

import Data.Monoid
import Data.String

import Syntax.Abstract
import Syntax.Annotation
import Syntax.Module
import Syntax.Name
import Util

pattern BuiltinModuleName :: ModuleName
pattern BuiltinModuleName <- ((==) "Sixten.Builtin" -> True) where BuiltinModuleName = "Sixten.Builtin"

pattern UnsolvedConstraintName :: QName
pattern UnsolvedConstraintName <- ((==) "Sixten.Builtin.UnsolvedConstraint" -> True) where UnsolvedConstraintName = "Sixten.Builtin.UnsolvedConstraint"

pattern IntName :: QName
pattern IntName <- ((==) "Sixten.Builtin.int" -> True) where IntName = "Sixten.Builtin.int"
pattern IntType :: Expr t
pattern IntType = Global IntName

pattern ByteName :: QName
pattern ByteName <- ((==) "Sixten.Builtin.byte" -> True) where ByteName = "Sixten.Builtin.byte"
pattern ByteType :: Expr t
pattern ByteType = Global ByteName

pattern AddIntName :: QName
pattern AddIntName <- ((==) "Sixten.Builtin.addInt" -> True) where AddIntName = "Sixten.Builtin.addInt"
pattern AddInt :: Expr t -> Expr t -> Expr t
pattern AddInt e1 e2 = App (App (Global AddIntName) Explicit e1) Explicit e2

pattern SubIntName :: QName
pattern SubIntName <- ((==) "Sixten.Builtin.subInt" -> True) where SubIntName = "Sixten.Builtin.subInt"
pattern SubInt :: Expr t -> Expr t -> Expr t
pattern SubInt e1 e2 = App (App (Global SubIntName) Explicit e1) Explicit e2

pattern MaxIntName :: QName
pattern MaxIntName <- ((==) "Sixten.Builtin.maxInt" -> True) where MaxIntName = "Sixten.Builtin.maxInt"
pattern MaxInt :: Expr t -> Expr t -> Expr t
pattern MaxInt e1 e2 = App (App (Global MaxIntName) Explicit e1) Explicit e2

pattern TypeName :: QName
pattern TypeName <- ((==) "Sixten.Builtin.type" -> True) where TypeName = "Sixten.Builtin.type"
pattern Type :: Expr t
pattern Type = Global TypeName

pattern ProductTypeRepName :: QName
pattern ProductTypeRepName <- ((==) "Sixten.Builtin.productTypeRep" -> True) where ProductTypeRepName = "Sixten.Builtin.productTypeRep"
pattern ProductTypeRep :: Expr t -> Expr t -> Expr t
pattern ProductTypeRep e1 e2 = App (App (Global ProductTypeRepName) Explicit e1) Explicit e2

pattern SumTypeRepName :: QName
pattern SumTypeRepName <- ((==) "Sixten.Builtin.sumTypeRep" -> True) where SumTypeRepName = "Sixten.Builtin.sumTypeRep"
pattern SumTypeRep :: Expr t -> Expr t -> Expr t
pattern SumTypeRep e1 e2 = App (App (Global SumTypeRepName) Explicit e1) Explicit e2

pattern SizeOfName :: QName
pattern SizeOfName <- ((==) "Sixten.Builtin.sizeOf" -> True) where SizeOfName = "Sixten.Builtin.sizeOf"

pattern RefName :: Constr
pattern RefName <- ((==) "Ptr" -> True) where RefName = "Ptr"
pattern PtrName :: QName
pattern PtrName <- ((==) "Sixten.Builtin.ptr" -> True) where PtrName = "Sixten.Builtin.ptr"
pattern Ref :: QConstr
pattern Ref = QConstr PtrName RefName

pattern UnitName :: QName
pattern UnitName <- ((==) "Sixten.Builtin.unit" -> True) where UnitName = "Sixten.Builtin.unit"
pattern UnitType :: Expr t
pattern UnitType = Global UnitName
pattern MkUnitConstrName :: Constr
pattern MkUnitConstrName <- ((==) "Unit" -> True) where MkUnitConstrName = "Unit"
pattern MkUnitConstr :: QConstr
pattern MkUnitConstr = QConstr UnitName MkUnitConstrName
pattern MkUnit :: Expr t
pattern MkUnit = Con MkUnitConstr

pattern Closure :: QConstr
pattern Closure <- ((== "Sixten.Builtin.Closure") -> True) where Closure = "Sixten.Builtin.Closure"

pattern FailName :: QName
pattern FailName <- ((==) "Sixten.Builtin.fail" -> True) where FailName = "Sixten.Builtin.fail"
pattern Fail :: Expr t -> Expr t
pattern Fail t = App (Global FailName) Explicit t

pattern PiTypeName :: QName
pattern PiTypeName <- ((==) "Sixten.Builtin.pi" -> True) where PiTypeName = "Sixten.Builtin.pi"

pattern NatName :: QName
pattern NatName <- ((==) "Sixten.Builtin.nat" -> True) where NatName = "Sixten.Builtin.nat"
pattern Nat :: Expr t
pattern Nat = Global NatName

pattern ZeroName :: Constr
pattern ZeroName <- ((==) "Zero" -> True) where ZeroName = "Zero"
pattern ZeroConstr :: QConstr
pattern ZeroConstr = QConstr NatName ZeroName
pattern Zero :: Expr t
pattern Zero = Con ZeroConstr

pattern SuccName :: Constr
pattern SuccName <- ((==) "Succ" -> True) where SuccName = "Succ"
pattern SuccConstr :: QConstr
pattern SuccConstr = QConstr NatName SuccName
pattern Succ :: Expr t -> Expr t
pattern Succ x = App (Con SuccConstr) Explicit x

pattern StringName :: QName
pattern StringName <- ((==) "Sixten.Builtin.string" -> True) where StringName = "Sixten.Builtin.string"
pattern MkStringName :: Constr
pattern MkStringName <- ((==) "String" -> True) where MkStringName = "String"
pattern MkStringConstr :: QConstr
pattern MkStringConstr = QConstr StringName MkStringName

pattern ArrayName :: QName
pattern ArrayName <- ((==) "Sixten.Builtin.array" -> True) where ArrayName = "Sixten.Builtin.array"
pattern MkArrayName :: Constr
pattern MkArrayName <- ((==) "Array" -> True) where MkArrayName = "Array"
pattern MkArrayConstr :: QConstr
pattern MkArrayConstr = QConstr ArrayName MkArrayName

pattern PairName :: QName
pattern PairName <- ((==) "Sixten.Builtin.pair" -> True) where PairName = "Sixten.Builtin.pair"
pattern Pair :: Expr t
pattern Pair = Global PairName
pattern MkPairName :: Constr
pattern MkPairName <- ((==) "Pair" -> True) where MkPairName = "Pair"
pattern MkPairConstr :: QConstr
pattern MkPairConstr = QConstr PairName MkPairName
pattern MkPair :: Expr t -> Expr t -> Expr t
pattern MkPair a b = App (App (Con MkPairConstr) Explicit a) Explicit b

applyName :: Int -> QName
applyName n = fromString $ "Sixten.Builtin.apply_" <> shower n

papName :: Int -> Int -> QName
papName k m = fromString $ "Sixten.Builtin.pap_" <> shower k <> "_" <> shower m
