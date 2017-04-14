{-# LANGUAGE OverloadedStrings, ViewPatterns, MonadComprehensions, PatternSynonyms #-}
module Builtin where

import Control.Applicative
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.List.NonEmpty
import Data.Maybe
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import qualified Backend.LLVM as LLVM
import Backend.Target(Target)
import qualified Backend.Target as Target
import Syntax
import Syntax.Abstract as Abstract
import qualified Syntax.Sized.Closed as Closed
import qualified Syntax.Sized.Lifted as Lifted
import Util

pattern IntName <- ((==) "Int" -> True) where IntName = "Int"
pattern IntType = Global IntName

pattern ByteName <- ((==) "Byte" -> True) where ByteName = "Byte"
pattern ByteType = Global ByteName

pattern AddIntName <- ((==) "addInt" -> True) where AddIntName = "addInt"
pattern AddInt e1 e2 = App (App (Global AddIntName) Explicit e1) Explicit e2

pattern SubIntName <- ((==) "subInt" -> True) where SubIntName = "subInt"
pattern SubInt e1 e2 = App (App (Global SubIntName) Explicit e1) Explicit e2

pattern MaxIntName <- ((==) "maxInt" -> True) where MaxIntName = "maxInt"
pattern MaxInt e1 e2 = App (App (Global MaxIntName) Explicit e1) Explicit e2

pattern PrintIntName <- ((==) "printInt" -> True) where PrintIntName = "printInt"
pattern PrintInt e1 = App (Global PrintIntName) Explicit e1

pattern TypeName <- ((==) "Type" -> True) where TypeName = "Type"
pattern Type = Global TypeName

pattern SizeOfName <- ((==) "sizeOf" -> True) where SizeOfName = "sizeOf"

pattern RefName <- ((==) "Ref" -> True) where RefName = "Ref"
pattern PtrName <- ((==) "Ptr" -> True) where PtrName = "Ptr"

pattern UnitName <- ((==) "Unit" -> True) where UnitName = "Unit"
pattern UnitType = Global UnitName
pattern MkUnitConstrName <- ((==) "MkUnit" -> True) where MkUnitConstrName = "MkUnit"
pattern MkUnitConstr = QConstr UnitName MkUnitConstrName
pattern MkUnit = Con MkUnitConstr

pattern Closure <- ((== QConstr "Builtin" "CL") -> True) where Closure = QConstr "Builtin" "CL"

pattern Ref = QConstr PtrName RefName

pattern FailName <- ((==) "fail" -> True) where FailName = "fail"
pattern Fail t = App (Global FailName) Explicit t

pattern PiTypeName <- ((==) "Pi_" -> True) where PiTypeName = "Pi_"

pattern NatName <- ((==) "Nat" -> True) where NatName = "Nat"
pattern Nat = Global NatName

pattern ZeroName <- ((==) "Zero" -> True) where ZeroName = "Zero"
pattern ZeroConstr = QConstr NatName ZeroName
pattern Zero = Con ZeroConstr

pattern SuccName <- ((==) "Succ" -> True) where SuccName = "Succ"
pattern SuccConstr = QConstr NatName SuccName
pattern Succ x = App (Con SuccConstr) Explicit x

pattern StringName <- ((==) "String" -> True) where StringName = "String"
pattern MkStringName <- ((==) "MkString" -> True) where MkStringName = "MkString"
pattern MkStringConstr = QConstr StringName MkStringName

pattern ArrayName <- ((==) "Array" -> True) where ArrayName = "Array"
pattern MkArrayName <- ((==) "MkArray" -> True) where MkArrayName = "MkArray"
pattern MkArrayConstr = QConstr ArrayName MkArrayName

pattern TupleName <- ((==) "Tuple" -> True) where TupleName = "Tuple"
pattern Tuple = Global TupleName
pattern MkTupleName <- ((==) "MkTuple" -> True) where MkTupleName = "MkTuple"
pattern MkTupleConstr = QConstr TupleName MkTupleName
pattern MkTuple a b = App (App (Con MkTupleConstr) Explicit a) Explicit b

applyName :: Int -> Name
applyName n = "apply_" <> shower n

papName :: Int -> Int -> Name
papName k m = "pap_" <> shower k <> "_" <> shower m

addInt :: Expr v -> Expr v -> Expr v
addInt (Lit (Integer 0)) e = e
addInt e (Lit (Integer 0)) = e
addInt (Lit (Integer m)) (Lit (Integer n)) = Lit $ Integer $ m + n
addInt e e' = AddInt e e'

maxInt :: Expr v -> Expr v -> Expr v
maxInt (Lit (Integer 0)) e = e
maxInt e (Lit (Integer 0)) = e
maxInt (Lit (Integer m)) (Lit (Integer n)) = Lit $ Integer $ max m n
maxInt e e' = MaxInt e e'

context :: Target -> HashMap Name (Definition Expr Void, Type Void)
context target = HashMap.fromList
  [ (TypeName, opaqueData typeRep Type)
  , (SizeOfName, opaque $ arrow Explicit Type IntType)
  , (PtrName, dataType (Lam mempty Explicit Type $ Scope ptrSize)
                       (arrow Explicit Type Type)
                       [ ConstrDef RefName $ toScope $ fmap B $ arrow Explicit (pure 0)
                                           $ app (Global PtrName) Explicit (pure 0)
                       ])
  , (ByteName, opaqueData byteRep Type)
  , (IntName, opaqueData intRep Type)
  , (NatName, dataType intRep Type
      [ ConstrDef ZeroName $ Scope Nat
      , ConstrDef SuccName $ Scope $ arrow Explicit Nat Nat
      ])
  , (AddIntName, opaque $ arrow Explicit IntType $ arrow Explicit IntType IntType)
  , (SubIntName, opaque $ arrow Explicit IntType $ arrow Explicit IntType IntType)
  , (MaxIntName, opaque $ arrow Explicit IntType $ arrow Explicit IntType IntType)
  , (PrintIntName, opaque $ arrow Explicit IntType IntType)
  , (PiTypeName, opaqueData ptrSize Type)
  , (FailName, opaque $ namedPi "T" Explicit Type $ pure "T")
  ]
  where
    cl = fromMaybe (error "Builtin not closed") . closed
    opaqueData sz t = dataType sz t mempty
    opaque t = (Opaque, cl t)
    dataType sz t xs = (DataDefinition (DataDef xs) sz, cl t)
    namedPi :: Name -> Plicitness -> Type Name -> Expr Name -> Expr Name
    namedPi n p t e = Pi (fromName n) p t $ abstract1 n e
    byteRep = Lit $ Integer 1
    intRep = Lit $ Integer $ Target.intBytes target
    ptrSize = Lit $ Integer $ Target.ptrBytes target
    typeRep = intRep

convertedContext :: Target -> HashMap Name (Lifted.Definition Closed.Expr Void)
convertedContext target = HashMap.fromList $ concat
  [[( TypeName
    , constDef $ Closed.Sized intSize intSize
    )
  , (SizeOfName
    , funDef (Telescope $ pure (mempty, (), Scope $ global TypeName))
      $ Scope $ Closed.Sized intSize $ pure $ B 0
    )
  , ( PiTypeName
    , constDef $ Closed.Sized intSize ptrSize
    )
  , ( PtrName
    , funDef (Telescope $ pure (mempty, (), Scope $ global TypeName))
      $ Scope $ Closed.Sized intSize ptrSize
    )
  , ( IntName
    , constDef $ Closed.Sized intSize intSize
    )
  , ( ByteName
    , constDef $ Closed.Sized intSize byteSize
    )
  , ( AddIntName
    , funDef
        (Telescope
        $ Vector.fromList [ (mempty, (), Scope intSize)
                          , (mempty, (), Scope intSize)
                          ])
      $ Scope
      $ Closed.Sized intSize
      $ Closed.Prim
      $ Primitive (Direct $ Target.intBytes target)
      [TextPart $ "add " <> intT <> " "
      , pure $ Closed.Var $ B 0
      , ", "
      , pure $ Closed.Var $ B 1
      ]
    )
  , ( SubIntName
    , funDef
        (Telescope
        $ Vector.fromList [ (mempty, (), Scope intSize)
                          , (mempty, (), Scope intSize)
                          ])
      $ Scope
      $ Closed.Sized intSize
      $ Closed.Prim
      $ Primitive (Direct $ Target.intBytes target)
      [TextPart $ "sub " <> intT <> " "
      , pure $ Closed.Var $ B 0
      , ", "
      , pure $ Closed.Var $ B 1
      ]
    )
  , ( MaxIntName
    , funDef
        (Telescope
        $ Vector.fromList [ (mempty, (), Scope intSize)
                          , (mempty, (), Scope intSize)
                          ])
      $ Scope
      $ Closed.Sized intSize
      $ Closed.Let "gt"
      (Closed.Sized intSize
      $ Closed.Prim
      $ Primitive (Direct $ Target.intBytes target)
      [TextPart $ "icmp ugt " <> intT <> " ", pure $ Closed.Var $ B 0, ", ", pure $ Closed.Var $ B 1])
      $ toScope
      $ Closed.Prim
      $ Primitive (Direct $ Target.intBytes target)
      ["select i1 ", pure $ Closed.Var $ B ()
      , TextPart $ ", " <> intT <> " "
      , pure $ Closed.Var $ F $ B 0
      , TextPart $ ", " <> intT <> " "
      , pure $ Closed.Var $ F $ B 1
      ]
    )
  , ( PrintIntName
    , funDef
        (Telescope
        $ Vector.fromList [(mempty, (), Scope intSize)])
      $ Scope
      $ Closed.Sized intSize
      $ Closed.Let "res"
      (Closed.Sized intSize
      $ Closed.Prim
      $ Primitive (Direct $ Target.intBytes target)
      [TextPart $ "call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @size_t-format, i32 0, i32 0), " <> intT <> " "
      , pure $ Closed.Var $ B 0, ")"
      ])
      $ Scope
      $ Closed.Lit $ Integer 0
    )
  , ( FailName
    , funDef
        (Telescope
        $ Vector.fromList [(mempty, (), Scope intSize)])
      $ Scope
      $ Closed.Sized (Closed.Var $ B 0)
      $ Closed.Prim
      $ Primitive (Direct 0)
      [TextPart $ "call " <> voidT <> " @exit(i32 1)"]
    )
  ]
  , [(papName left given, pap target left given) | given <- [1..maxArity - 1], left <- [1..maxArity - given]]
  , [(applyName arity, apply target arity) | arity <- [1..maxArity]]
  ]
  where
    intT = LLVM.integerT
    voidT = LLVM.voidT
    constDef = Lifted.ConstantDef Public . Lifted.Constant
    funDef tele = Lifted.FunctionDef Public Lifted.NonClosure . Lifted.Function tele
    intSize = Closed.Lit $ Integer $ Target.intBytes target
    byteSize = Closed.Lit $ Integer 1
    ptrSize = Closed.Lit $ Integer $ Target.ptrBytes target

convertedSignatures :: Target -> HashMap Name Closed.FunSignature
convertedSignatures target
  = flip HashMap.mapMaybeWithKey (convertedContext target) $ \name def ->
    case def of
      Lifted.FunctionDef _ _ (Lifted.Function tele s) -> case fromScope s of
        Closed.Anno _ t -> Just (tele, toScope t)
        _ -> error $ "Builtin.convertedSignatures " <> show name
      Lifted.ConstantDef _ _ -> Nothing

deref :: Target -> Closed.Expr v -> Closed.Expr v
deref target e
  = Closed.Case (Closed.Sized intSize e)
  $ ConBranches
  $ pure
    ( Ref
    , Telescope
      $ pure ("dereferenced", (), Scope unknownSize)
    , toScope
    $ Closed.Var $ B 0
    )
  where
    unknownSize = global "Builtin.deref.UnknownSize"
    intSize = Closed.Lit $ Integer $ Target.ptrBytes target

maxArity :: Num n => n
maxArity = 6

apply :: Target -> Int -> Lifted.Definition Closed.Expr Void
apply target numArgs
  = Lifted.FunctionDef Public Lifted.NonClosure
  $ Lifted.Function
    (Telescope
    $ Vector.cons ("this", (), Scope ptrSize)
    $ (\n -> (fromText $ "size" <> shower (unTele n), (), Scope intSize)) <$> Vector.enumFromN 0 numArgs
    <|> (\n -> (fromText $ "x" <> shower (unTele n), (), Scope $ pure $ B $ 1 + n)) <$> Vector.enumFromN 0 numArgs)
  $ toScope
  $ Closed.Sized (Closed.Global "Builtin.apply.unknownSize")
  $ Closed.Case (deref target $ Closed.Var $ B 0)
  $ ConBranches
  $ pure
    ( Closure
    , Telescope
      $ Vector.fromList [("f_unknown", (), Scope ptrSize), ("n", (), Scope intSize)]
    , toScope
      $ Closed.Case (Closed.Sized intSize $ Closed.Var $ B 1)
      $ LitBranches
        [(Integer $ fromIntegral arity, br arity) | arity <- 1 :| [2..maxArity]]
        $ Closed.Call (global FailName) $ pure $ Closed.Sized intSize (Closed.Lit $ Integer 1)
    )
  where
    intSize = Closed.Lit $ Integer $ Target.intBytes target
    ptrSize = Closed.Lit $ Integer $ Target.ptrBytes target

    directPtr = Direct $ Target.ptrBytes target
    directInt = Direct $ Target.intBytes target

    br :: Int -> Closed.Expr (Var Tele (Var Tele Void))
    br arity
      | numArgs < arity
        = Closed.Con Ref
        $ pure
        $ sizedCon target (Closed.Lit $ Integer 0) Closure
        $ Vector.cons (Closed.Sized ptrSize $ global $ papName (arity - numArgs) numArgs)
        $ Vector.cons (Closed.Sized intSize $ Closed.Lit $ Integer $ fromIntegral $ arity - numArgs)
        $ Vector.cons (Closed.Sized ptrSize $ Closed.Var $ F $ B 0)
        $ (\n -> Closed.Sized intSize $ Closed.Var $ F $ B $ 1 + n) <$> Vector.enumFromN 0 numArgs
        <|> (\n -> Closed.Sized (Closed.Var $ F $ B $ 1 + n) $ Closed.Var $ F $ B $ 1 + Tele numArgs + n) <$> Vector.enumFromN 0 numArgs
      | numArgs == arity
        = Closed.PrimCall (ReturnIndirect OutParam) (Closed.Var $ B 0)
        $ Vector.cons (Closed.Sized ptrSize $ Closed.Var $ F $ B 0, directPtr)
        $ (\n -> (Closed.Sized intSize $ Closed.Var $ F $ B $ 1 + n, directInt)) <$> Vector.enumFromN 0 numArgs
        <|> (\n -> (Closed.Sized (Closed.Var $ F $ B $ 1 + n) $ Closed.Var $ F $ B $ 1 + Tele numArgs + n, Indirect)) <$> Vector.enumFromN 0 numArgs
      | otherwise
        = Closed.Call (global $ applyName $ numArgs - arity)
        $ Vector.cons
          (Closed.Sized ptrSize
          $ Closed.PrimCall (ReturnIndirect OutParam) (Closed.Var $ B 0)
          $ Vector.cons (Closed.Sized ptrSize $ Closed.Var $ F $ B 0, directPtr)
          $ (\n -> (Closed.Sized intSize $ Closed.Var $ F $ B $ 1 + n, directInt)) <$> Vector.enumFromN 0 arity
          <|> (\n -> (Closed.Sized (Closed.Var $ F $ B $ 1 + n) $ Closed.Var $ F $ B $ 1 + fromIntegral numArgs + n, Indirect)) <$> Vector.enumFromN 0 arity)
        $ (\n -> Closed.Sized intSize $ Closed.Var $ F $ B $ 1 + n) <$> Vector.enumFromN (fromIntegral arity) (numArgs - arity)
        <|> (\n -> Closed.Sized (Closed.Var $ F $ B $ 1 + n) $ Closed.Var $ F $ B $ 1 + fromIntegral numArgs + n) <$> Vector.enumFromN (fromIntegral arity) (numArgs - arity)

pap :: Target -> Int -> Int -> Lifted.Definition Closed.Expr Void
pap target k m
  = Lifted.FunctionDef Public Lifted.NonClosure
  $ Lifted.Function
    (Telescope
    $ Vector.cons ("this", (), Scope intSize)
    $ (\n -> (fromText $ "size" <> shower (unTele n), (), Scope intSize)) <$> Vector.enumFromN 0 k
    <|> (\n -> (fromText $ "x" <> shower (unTele n), (), Scope $ pure $ B $ 1 + n)) <$> Vector.enumFromN 0 k)
  $ toScope
  $ Closed.Sized (Closed.Global "Builtin.pap.unknownSize")
  $ Closed.Case (deref target $ Closed.Var $ B 0)
  $ ConBranches
  $ pure
    ( Closure
    , Telescope
      $ Vector.cons ("_", (), Scope intSize)
      $ Vector.cons ("_", (), Scope intSize)
      $ Vector.cons ("that", (), Scope intSize)
      $ (\n -> (fromText $ "size" <> shower (unTele n), (), Scope intSize)) <$> Vector.enumFromN 0 m
      <|> (\n -> (fromText $ "y" <> shower (unTele n), (), Scope $ pure $ B $ 3 + n)) <$> Vector.enumFromN 0 m
    , toScope
      $ Closed.Call (global $ applyName $ m + k)
      $ Vector.cons (Closed.Sized ptrSize $ Closed.Var $ B 2)
      $ (\n -> Closed.Sized intSize $ Closed.Var $ B $ 3 + n) <$> Vector.enumFromN 0 m
      <|> (\n -> Closed.Sized intSize $ Closed.Var $ F $ B $ 1 + n) <$> Vector.enumFromN 0 k
      <|> (\n -> Closed.Sized (Closed.Var $ B $ 3 + n) $ Closed.Var $ B $ 3 + Tele m + n) <$> Vector.enumFromN 0 m
      <|> (\n -> Closed.Sized (Closed.Var $ F $ B $ 1 + n) $ Closed.Var $ F $ B $ 1 + Tele k + n) <$> Vector.enumFromN 0 k
    )
  where
    intSize = Closed.Lit $ Integer $ Target.intBytes target
    ptrSize = Closed.Lit $ Integer $ Target.ptrBytes target

addInts :: Target -> Vector (Closed.Expr v) -> Closed.Expr v
addInts target = Vector.foldr1 go
  where
    go x y
      = Closed.Call (global AddIntName)
      $ Vector.cons (Closed.Anno x intSize)
      $ pure $ Closed.Anno y intSize
    intSize = Closed.Lit $ Integer $ Target.intBytes target

sizedCon :: Target -> Closed.Expr v -> QConstr -> Vector (Closed.Expr v) -> Closed.Expr v
sizedCon target tagSize qc args
  = Closed.Sized (addInts target $ Vector.cons tagSize argSizes) (Closed.Con qc args)
  where
    argSizes = Closed.sizeOf <$> args
