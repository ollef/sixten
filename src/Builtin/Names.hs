{-# LANGUAGE OverloadedStrings, PatternSynonyms, ViewPatterns #-}
module Builtin.Names where

import Protolude hiding (Type)

import Data.String

import Syntax.Core
import Syntax.Annotation
import Syntax.QName
import Syntax.Name
import Util

pattern BuiltinModuleName :: ModuleName
pattern BuiltinModuleName <- ((==) "Sixten.Builtin" -> True) where BuiltinModuleName = "Sixten.Builtin"

pattern StaticErrorName :: QName
pattern StaticErrorName <- ((==) "Sixten.Builtin.StaticError" -> True) where StaticErrorName = "Sixten.Builtin.StaticError"

pattern QGlobal :: QName -> Expr m t
pattern QGlobal n = Global (GName n Mempty)

pattern IntName :: QName
pattern IntName <- ((==) "Sixten.Builtin.Int" -> True) where IntName = "Sixten.Builtin.Int"
pattern IntType :: Expr m t
pattern IntType = Global (GName IntName Mempty)

pattern ByteName :: QName
pattern ByteName <- ((==) "Sixten.Builtin.Byte" -> True) where ByteName = "Sixten.Builtin.Byte"
pattern ByteType :: Expr m t
pattern ByteType = Global (GName ByteName Mempty)

pattern AddIntName :: QName
pattern AddIntName <- ((==) "Sixten.Builtin.addInt" -> True) where AddIntName = "Sixten.Builtin.addInt"
pattern AddInt :: Expr m t -> Expr m t -> Expr m t
pattern AddInt e1 e2 = App (App (Global (GName AddIntName Mempty)) Explicit e1) Explicit e2

pattern SubIntName :: QName
pattern SubIntName <- ((==) "Sixten.Builtin.subInt" -> True) where SubIntName = "Sixten.Builtin.subInt"
pattern SubInt :: Expr m t -> Expr m t -> Expr m t
pattern SubInt e1 e2 = App (App (Global (GName SubIntName Mempty)) Explicit e1) Explicit e2

pattern MaxIntName :: QName
pattern MaxIntName <- ((==) "Sixten.Builtin.maxInt" -> True) where MaxIntName = "Sixten.Builtin.maxInt"
pattern MaxInt :: Expr m t -> Expr m t -> Expr m t
pattern MaxInt e1 e2 = App (App (Global (GName MaxIntName Mempty)) Explicit e1) Explicit e2

pattern TypeName :: QName
pattern TypeName <- ((==) "Sixten.Builtin.Type" -> True) where TypeName = "Sixten.Builtin.Type"
pattern Type :: Expr m t
pattern Type = Global (GName TypeName Mempty)

pattern MkTypeName :: QName
pattern MkTypeName <- ((==) "Sixten.Builtin.MkType" -> True) where MkTypeName = "Sixten.Builtin.MkType"

pattern ProductTypeRepName :: QName
pattern ProductTypeRepName <- ((==) "Sixten.Builtin.productTypeRep" -> True) where ProductTypeRepName = "Sixten.Builtin.productTypeRep"
pattern ProductTypeRep :: Expr m t -> Expr m t -> Expr m t
pattern ProductTypeRep e1 e2 = App (App (Global (GName ProductTypeRepName Mempty)) Explicit e1) Explicit e2

pattern SumTypeRepName :: QName
pattern SumTypeRepName <- ((==) "Sixten.Builtin.sumTypeRep" -> True) where SumTypeRepName = "Sixten.Builtin.sumTypeRep"
pattern SumTypeRep :: Expr m t -> Expr m t -> Expr m t
pattern SumTypeRep e1 e2 = App (App (Global (GName SumTypeRepName Mempty)) Explicit e1) Explicit e2

pattern SizeOfName :: QName
pattern SizeOfName <- ((==) "Sixten.Builtin.sizeOf" -> True) where SizeOfName = "Sixten.Builtin.sizeOf"

pattern EqualsName :: QName
pattern EqualsName <- ((==) "Sixten.Builtin.__Equals__" -> True) where EqualsName = "Sixten.Builtin.__Equals__"
pattern Equals :: Type m t -> Expr m t -> Expr m t -> Expr m t
pattern Equals typ e1 e2 =
  App (App (App (Global (GName EqualsName Mempty)) Implicit typ) Explicit e1) Explicit e2

pattern ReflConstrName :: Constr
pattern ReflConstrName <- ((==) "__Refl__" -> True) where ReflConstrName = "__Refl__"
pattern ReflConstr :: QConstr
pattern ReflConstr = QConstr EqualsName ReflConstrName
pattern Refl :: Type m t -> Expr m t -> Expr m t -> Expr m t
pattern Refl typ e1 e2 =
  App (App (App (Con ReflConstr) Implicit typ) Implicit e1) Implicit e2

pattern UnitName :: QName
pattern UnitName <- ((==) "Sixten.Builtin.Unit" -> True) where UnitName = "Sixten.Builtin.Unit"
pattern UnitType :: Expr m t
pattern UnitType = Global (GName UnitName Mempty)
pattern MkUnitConstrName :: Constr
pattern MkUnitConstrName <- ((==) "MkUnit" -> True) where MkUnitConstrName = "MkUnit"
pattern MkUnitConstr :: QConstr
pattern MkUnitConstr = QConstr UnitName MkUnitConstrName
pattern MkUnit :: Expr m t
pattern MkUnit = Con MkUnitConstr

pattern Closure :: QConstr
pattern Closure <- ((== "Sixten.Builtin.Closure.MkClosure") -> True) where Closure = "Sixten.Builtin.Closure.MkClosure"

pattern FailName :: QName
pattern FailName <- ((==) "Sixten.Builtin.fail" -> True) where FailName = "Sixten.Builtin.fail"
pattern Fail :: Expr m t -> Expr m t
pattern Fail t = App (Global (GName FailName Mempty)) Explicit t

pattern PiTypeName :: QName
pattern PiTypeName <- ((==) "Sixten.Builtin.Pi_" -> True) where PiTypeName = "Sixten.Builtin.Pi_"

pattern NatName :: QName
pattern NatName <- ((==) "Sixten.Builtin.Nat" -> True) where NatName = "Sixten.Builtin.Nat"
pattern Nat :: Expr m t
pattern Nat = Global (GName NatName Mempty)

pattern ZeroName :: Constr
pattern ZeroName <- ((==) "Zero" -> True) where ZeroName = "Zero"
pattern ZeroConstr :: QConstr
pattern ZeroConstr = QConstr NatName ZeroName
pattern Zero :: Expr m t
pattern Zero = Con ZeroConstr

pattern SuccName :: Constr
pattern SuccName <- ((==) "Succ" -> True) where SuccName = "Succ"
pattern SuccConstr :: QConstr
pattern SuccConstr = QConstr NatName SuccName
pattern Succ :: Expr m t -> Expr m t
pattern Succ x = App (Con SuccConstr) Explicit x

pattern StringName :: QName
pattern StringName <- ((==) "Sixten.Builtin.String" -> True) where StringName = "Sixten.Builtin.String"
pattern StringType :: Expr m t
pattern StringType = Global (GName StringName Mempty)
pattern MkStringName :: Constr
pattern MkStringName <- ((==) "MkString" -> True) where MkStringName = "MkString"
pattern MkStringConstr :: QConstr
pattern MkStringConstr = QConstr StringName MkStringName

pattern ArrayName :: QName
pattern ArrayName <- ((==) "Sixten.Builtin.Array" -> True) where ArrayName = "Sixten.Builtin.Array"
pattern MkArrayName :: Constr
pattern MkArrayName <- ((==) "MkArray" -> True) where MkArrayName = "MkArray"
pattern MkArrayConstr :: QConstr
pattern MkArrayConstr = QConstr ArrayName MkArrayName

pattern VectorName :: QName
pattern VectorName <- ((==) "Sixten.Builtin.Vector" -> True) where VectorName = "Sixten.Builtin.Vector"

pattern PairName :: QName
pattern PairName <- ((==) "Sixten.Builtin.Pair" -> True) where PairName = "Sixten.Builtin.Pair"
pattern Pair :: Expr m t
pattern Pair = Global (GName PairName Mempty)
pattern MkPairName :: Constr
pattern MkPairName <- ((==) "MkPair" -> True) where MkPairName = "MkPair"
pattern MkPairConstr :: QConstr
pattern MkPairConstr = QConstr PairName MkPairName
pattern MkPair :: Expr m t -> Expr m t -> Expr m t
pattern MkPair a b = App (App (Con MkPairConstr) Explicit a) Explicit b

pattern RuntimeModuleName :: ModuleName
pattern RuntimeModuleName <- ((==) "Sixten.Runtime" -> True) where RuntimeModuleName = "Sixten.Runtime"

applyName :: Int -> QName
applyName n = fromString $ "Sixten.Runtime.apply_" <> shower n

papName :: Int -> Int -> QName
papName k m = fromString $ "Sixten.Runtime.pap_" <> shower k <> "_" <> shower m
