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
import Syntax
import Syntax.Abstract as Abstract
import qualified Syntax.Sized.Closed as Closed
import qualified Syntax.Sized.Lifted as Lifted
import Util

pattern IntName <- ((==) "Int" -> True) where IntName = "Int"
pattern IntType = Global IntName

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

pattern UnitName <- ((==) "Unit_" -> True) where UnitName = "Unit_"
pattern UnitConstrName <- ((==) "unit_" -> True) where UnitConstrName = "unit_"
pattern Unit = QConstr UnitName UnitConstrName

pattern Closure <- ((== QConstr "Builtin" "CL") -> True) where Closure = QConstr "Builtin" "CL"

pattern Ref <- ((== QConstr PtrName RefName) -> True) where Ref = QConstr PtrName RefName

pattern FailName <- ((==) "fail" -> True) where FailName = "fail"
pattern Fail t = App (Global FailName) Explicit t

pattern PiTypeName <- ((==) "Pi_" -> True) where PiTypeName = "Pi_"

applyName :: Int -> Name
applyName n = "apply_" <> shower n

papName :: Int -> Int -> Name
papName k m = "pap_" <> shower k <> "_" <> shower m

addInt :: Expr v -> Expr v -> Expr v
addInt (Lit 0) e = e
addInt e (Lit 0) = e
addInt (Lit m) (Lit n) = Lit $ m + n
addInt e e' = AddInt e e'

maxInt :: Expr v -> Expr v -> Expr v
maxInt (Lit 0) e = e
maxInt e (Lit 0) = e
maxInt (Lit m) (Lit n) = Lit $ max m n
maxInt e e' = MaxInt e e'

context :: HashMap Name (Definition Expr Void, Type Void)
context = HashMap.fromList
  [ (TypeName, opaque (Lit 1) Type)
  , (SizeOfName, opaque piRep $ arrow Explicit Type IntType)
  , (PtrName, dataType (Lam mempty Explicit Type $ Scope $ Lit 1)
                       (arrow Explicit Type Type)
                       [ ConstrDef RefName $ toScope $ fmap B $ arrow Explicit (pure 0)
                                           $ app (Global PtrName) Explicit (pure 0)
                       ])
  , (IntName, opaque (Lit 1) Type)
  , (AddIntName, opaque piRep $ arrow Explicit IntType $ arrow Explicit IntType IntType)
  , (SubIntName, opaque piRep $ arrow Explicit IntType $ arrow Explicit IntType IntType)
  , (MaxIntName, opaque piRep $ arrow Explicit IntType $ arrow Explicit IntType IntType)
  , (PrintIntName, opaque piRep $ arrow Explicit IntType IntType)
  , (PiTypeName, opaque (Lit 1) Type)
  , (UnitName, dataType (Lit 0)
                        Type
                        [ConstrDef UnitConstrName $ toScope $ Global UnitName])
  , ( FailName , opaque piRep $ namedPi "T" Explicit Type $ pure "T")
  ]
  where
    piRep = Global PiTypeName
    cl = fromMaybe (error "Builtin not closed") . closed
    opaque sz t = dataType sz t mempty
    dataType sz t xs = (DataDefinition (DataDef xs) sz, cl t)
    namedPi :: Name -> Plicitness -> Type Name -> Expr Name -> Expr Name
    namedPi n p t e = Pi (fromName n) p t $ abstract1 n e

convertedContext :: HashMap Name (Lifted.Definition Closed.Expr Void)
convertedContext = HashMap.fromList $ concat
  [[( TypeName
    , constDef $ Closed.sized 1 $ Closed.Lit 1
    )
  , (SizeOfName
    , funDef (Telescope $ pure (mempty, (), slit 1))
      $ Scope $ Closed.sized 1 $ pure $ B 0
    )
  , ( PiTypeName
    , constDef $ Closed.sized 1 $ Closed.Lit 1
    )
  , ( PtrName
    , funDef (Telescope $ pure (mempty, (), slit 1))
      $ Scope $ Closed.sized 1 $ Closed.Lit 1
    )
  , ( IntName
    , constDef $ Closed.sized 1 $ Closed.Lit 1
    )
  , ( AddIntName
    , funDef
        (Telescope
        $ Vector.fromList [ (mempty, (), slit 1)
                          , (mempty, (), slit 1)
                          ])
      $ Scope
      $ Closed.sized 1
      $ Closed.Prim
      $ Primitive Direct
      [TextPart $ "add " <> intT <> " "
      , pure $ Closed.Var $ B 0
      , ", "
      , pure $ Closed.Var $ B 1
      ]
    )
  , ( SubIntName
    , funDef
        (Telescope
        $ Vector.fromList [ (mempty, (), slit 1)
                          , (mempty, (), slit 1)
                          ])
      $ Scope
      $ Closed.sized 1
      $ Closed.Prim
      $ Primitive Direct
      [TextPart $ "sub " <> intT <> " "
      , pure $ Closed.Var $ B 0
      , ", "
      , pure $ Closed.Var $ B 1
      ]
    )
  , ( MaxIntName
    , funDef
        (Telescope
        $ Vector.fromList [ (mempty, (), slit 1)
                          , (mempty, (), slit 1)
                          ])
      $ Scope
      $ Closed.sized 1
      $ Closed.Let "lt"
      (Closed.sized 1
      $ Closed.Prim
      $ Primitive Direct
      [TextPart $ "icmp ugt " <> intT <> " ", pure $ Closed.Var $ B 0, ", ", pure $ Closed.Var $ B 1])
      $ toScope
      $ Closed.Prim
      $ Primitive Direct
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
        $ Vector.fromList [(mempty, (), slit 1)])
      $ Scope
      $ Closed.sized 1
      $ Closed.Let "res"
      (Closed.sized 1
      $ Closed.Prim
      $ Primitive Direct
      [TextPart $ "call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @size_t-format, i32 0, i32 0), " <> intT <> " "
      , pure $ Closed.Var $ B 0, ")"
      ])
      $ Scope
      $ Closed.Lit 0
    )
  , ( UnitName
    , constDef $ Closed.sized 1 $ Closed.Lit 0
    )
  , ( FailName
    , funDef
        (Telescope
        $ Vector.fromList [(mempty, (), slit 1)])
      $ Scope
      $ flip Closed.Anno (Closed.Var $ B 0)
      $ Closed.Prim
      $ Primitive Void
      [TextPart $ "call " <> voidT <> " @exit(i32 1)"]
    )
  ]
  , [(papName left given, pap left given) | given <- [1..maxArity - 1], left <- [1..maxArity - given]]
  , [(applyName arity, apply arity) | arity <- [1..maxArity]]
  ]
  where
    intT = LLVM.integerT
    voidT = LLVM.voidT
    constDef = Lifted.ConstantDef Public . Lifted.Constant
    funDef tele = Lifted.FunctionDef Public Lifted.NonClosure . Lifted.Function tele

convertedSignatures :: HashMap Name Closed.FunSignature
convertedSignatures = flip HashMap.mapMaybeWithKey convertedContext $ \name def ->
  case def of
    Lifted.FunctionDef _ _ (Lifted.Function tele s) -> case fromScope s of
      Closed.Anno _ t -> Just (tele, toScope t)
      _ -> error $ "Builtin.convertedSignatures " <> show name
    Lifted.ConstantDef _ _ -> Nothing

-- TODO move these
slit :: Literal -> Scope b Closed.Expr v
slit n = Scope $ Closed.Lit n

svarb :: b -> Scope b Closed.Expr a
svarb = Scope . Closed.Var . B

maxArity :: Num n => n
maxArity = 6

deref :: Closed.Expr v -> Closed.Expr v
deref e
  = Closed.Case (Closed.sized 1 e)
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

apply :: Int -> Lifted.Definition Closed.Expr Void
apply numArgs
  = Lifted.FunctionDef Public Lifted.NonClosure
  $ Lifted.Function
    (Telescope
    $ Vector.cons ("this", (), slit 1)
    $ (\n -> (fromText $ "size" <> shower (unTele n), (), slit 1)) <$> Vector.enumFromN 0 numArgs
    <|> (\n -> (fromText $ "x" <> shower (unTele n), (), svarb $ 1 + n)) <$> Vector.enumFromN 0 numArgs)
  $ toScope
  $ flip Closed.Anno (Closed.Global "Builtin.apply.unknownSize")
  $ Closed.Case (deref $ Closed.Var $ B 0)
  $ ConBranches
  $ pure
    ( Closure
    , Telescope
      $ Vector.fromList [("f_unknown", (), slit 1), ("n", (), slit 1)]
    , toScope
      $ Closed.Case (Closed.sized 1 $ Closed.Var $ B 1)
      $ LitBranches
        [(fromIntegral arity, br arity) | arity <- 1 :| [2..maxArity]]
        $ Closed.Call (global FailName) $ pure $ Closed.sized 1 (Closed.Lit 1)
    )
  where
    br :: Int -> Closed.Expr (Var Tele (Var Tele Void))
    br arity
      | numArgs < arity
        = Closed.Con Ref
        $ pure
        $ flip Closed.Anno
          (addInts
          $ Vector.cons (Closed.Lit $ fromIntegral $ 3 + numArgs)
          $ (\n -> Closed.Var $ F $ B $ 1 + n) <$> Vector.enumFromN 0 numArgs)
        $ Closed.Con Closure
        $ Vector.cons (Closed.sized 1 $ global $ papName (arity - numArgs) numArgs)
        $ Vector.cons (Closed.sized 1 $ Closed.Lit $ fromIntegral $ arity - numArgs)
        $ Vector.cons (Closed.sized 1 $ Closed.Var $ F $ B 0)
        $ (\n -> Closed.sized 1 $ Closed.Var $ F $ B $ 1 + n) <$> Vector.enumFromN 0 numArgs
        <|> (\n -> flip Closed.Anno (Closed.Var $ F $ B $ 1 + n) $ Closed.Var $ F $ B $ 1 + Tele numArgs + n) <$> Vector.enumFromN 0 numArgs
      | numArgs == arity
        = Closed.PrimCall (ReturnIndirect OutParam) (Closed.Var $ B 0)
        $ Vector.cons (Closed.sized 1 $ Closed.Var $ F $ B 0, Direct)
        $ (\n -> (Closed.sized 1 $ Closed.Var $ F $ B $ 1 + n, Direct)) <$> Vector.enumFromN 0 numArgs
        <|> (\n -> (flip Closed.Anno (Closed.Var $ F $ B $ 1 + n) $ Closed.Var $ F $ B $ 1 + Tele numArgs + n, Indirect)) <$> Vector.enumFromN 0 numArgs
      | otherwise
        = Closed.Call (global $ applyName $ numArgs - arity)
        $ Vector.cons
          (Closed.sized 1
          $ Closed.PrimCall (ReturnIndirect OutParam) (Closed.Var $ B 0)
          $ Vector.cons (Closed.sized 1 $ Closed.Var $ F $ B 0, Direct)
          $ (\n -> (Closed.sized 1 $ Closed.Var $ F $ B $ 1 + n, Direct)) <$> Vector.enumFromN 0 arity
          <|> (\n -> (flip Closed.Anno (Closed.Var $ F $ B $ 1 + n) $ Closed.Var $ F $ B $ 1 + fromIntegral numArgs + n, Indirect)) <$> Vector.enumFromN 0 arity)
        $ (\n -> Closed.sized 1 $ Closed.Var $ F $ B $ 1 + n) <$> Vector.enumFromN (fromIntegral arity) (numArgs - arity)
        <|> (\n -> flip Closed.Anno (Closed.Var $ F $ B $ 1 + n) $ Closed.Var $ F $ B $ 1 + fromIntegral numArgs + n) <$> Vector.enumFromN (fromIntegral arity) (numArgs - arity)

addInts :: Vector (Closed.Expr v) -> Closed.Expr v
addInts = Vector.foldr1 go
  where
    go x y
      = Closed.Call (global AddIntName)
      $ Vector.cons (Closed.Anno x $ Closed.Lit 1)
      $ pure $ Closed.Anno y (Closed.Lit 1)

pap :: Int -> Int -> Lifted.Definition Closed.Expr Void
pap k m
  = Lifted.FunctionDef Public Lifted.NonClosure
  $ Lifted.Function
    (Telescope
    $ Vector.cons ("this", (), slit 1)
    $ (\n -> (fromText $ "size" <> shower (unTele n), (), slit 1)) <$> Vector.enumFromN 0 k
    <|> (\n -> (fromText $ "x" <> shower (unTele n), (), svarb $ 1 + n)) <$> Vector.enumFromN 0 k)
  $ toScope
  $ flip Closed.Anno (Closed.Global "Builtin.pap.unknownSize")
  $ Closed.Case (deref $ Closed.Var $ B 0)
  $ ConBranches
  $ pure
    ( Closure
    , Telescope
      $ Vector.cons ("_", (), slit 1)
      $ Vector.cons ("_", (), slit 1)
      $ Vector.cons ("that", (), slit 1)
      $ (\n -> (fromText $ "size" <> shower (unTele n), (), slit 1)) <$> Vector.enumFromN 0 m
      <|> (\n -> (fromText $ "y" <> shower (unTele n), (), svarb $ 3 + n)) <$> Vector.enumFromN 0 m
    , toScope
      $ Closed.Call (global $ applyName $ m + k)
      $ Vector.cons (Closed.sized 1 $ Closed.Var $ B 2)
      $ (\n -> Closed.sized 1 $ Closed.Var $ B $ 3 + n) <$> Vector.enumFromN 0 m
      <|> (\n -> Closed.sized 1 $ Closed.Var $ F $ B $ 1 + n) <$> Vector.enumFromN 0 k
      <|> (\n -> flip Closed.Anno (Closed.Var $ B $ 3 + n) $ Closed.Var $ B $ 3 + Tele m + n) <$> Vector.enumFromN 0 m
      <|> (\n -> flip Closed.Anno (Closed.Var $ F $ B $ 1 + n) $ Closed.Var $ F $ B $ 1 + Tele k + n) <$> Vector.enumFromN 0 k
    )
