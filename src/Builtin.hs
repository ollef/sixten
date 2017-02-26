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
import qualified Syntax.Sized.Converted as Converted
import Util

pattern IntName <- ((==) "Int" -> True) where IntName = "Int"
pattern IntType = Global IntName

pattern AddIntName <- ((==) "addInt" -> True) where AddIntName = "addInt"
pattern AddIntE e1 e2 = AddInt Explicit Explicit e1 e2
pattern AddInt p1 p2 e1 e2 = App (App (Global AddIntName) p1 e1) p2 e2

pattern MaxIntName <- ((==) "maxInt" -> True) where MaxIntName = "maxInt"
pattern MaxIntE e1 e2 = MaxInt Explicit Explicit e1 e2
pattern MaxInt p1 p2 e1 e2 = App (App (Global MaxIntName) p1 e1) p2 e2

pattern PrintIntName <- ((==) "printInt" -> True) where PrintIntName = "printInt"
pattern PrintInt e1 = App (Global PrintIntName) Explicit e1

pattern TypeName <- ((==) "Type" -> True) where TypeName = "Type"
pattern Type = Global TypeName

pattern RefName <- ((==) "Ref" -> True) where RefName = "Ref"
pattern PtrName <- ((==) "Ptr" -> True) where PtrName = "Ptr"

pattern UnitName <- ((==) "Unit_" -> True) where UnitName = "Unit_"
pattern UnitConstrName <- ((==) "unit_" -> True) where UnitConstrName = "unit_"
pattern Unit = QConstr UnitName UnitConstrName

pattern Closure <- ((== QConstr "Builtin" "CL") -> True) where Closure = QConstr "Builtin" "CL"

pattern Ref <- ((== QConstr PtrName RefName) -> True) where Ref = QConstr PtrName RefName

pattern FailName <- ((==) "fail" -> True) where FailName = "fail"
pattern Fail t = App (Global FailName) Explicit t

applyName :: Int -> Name
applyName n = "apply_" <> shower n

papName :: Int -> Int -> Name
papName k m = "pap_" <> shower k <> "_" <> shower m

contextP :: HashMap Name (Definition ExprP Void, TypeP Void)
contextP = HashMap.fromList
  [ (TypeName, opaque Type)
  , (IntName, opaque Type)
  , (AddIntName, opaque $ arrow Explicit IntType $ arrow Explicit IntType IntType)
  , (MaxIntName, opaque $ arrow Explicit IntType $ arrow Explicit IntType IntType)
  , (PrintIntName, opaque $ arrow Explicit IntType IntType)
  , (PtrName, dataType (arrow Explicit Type Type)
                       [ ConstrDef RefName $ toScope $ fmap B $ arrow Explicit (pure 0)
                                           $ app (Global PtrName) Explicit (pure 0)
                       ])
  , (UnitName, dataType Type
                        [ConstrDef UnitConstrName $ toScope $ Global UnitName])

  , ( FailName
    , opaque
    $ namedPi "T" Explicit Type
    $ pure "T"
    )
  ]
  where
    cl = fromMaybe (error "Builtin not closed") . closed
    opaque t = (DataDefinition $ DataDef mempty, cl t)
    dataType t xs = (DataDefinition $ DataDef xs, cl t)
    namedPi :: Name -> Plicitness -> TypeP Name -> ExprP Name -> ExprP Name
    namedPi n p t e = Pi (fromName n) p t $ abstract1 n e

contextE :: HashMap Name (Definition ExprE Void, TypeE Void)
contextE = HashMap.fromList
  [ (TypeName, opaque Type)
  , (IntName, opaque Type)
  , (AddIntName, opaque $ arrow Retained IntType $ arrow Retained IntType IntType)
  , (MaxIntName, opaque $ arrow Retained IntType $ arrow Retained IntType IntType)
  , (PrintIntName, opaque $ arrow Retained IntType IntType)
  , (PtrName, dataType (arrow Retained Type Type)
                       [ ConstrDef RefName $ toScope $ fmap B $ arrow Retained (pure 0)
                                           $ app (Global PtrName) Retained (pure 0)
                       ])
  , (UnitName, dataType Type
                        [ConstrDef UnitConstrName $ toScope $ Global UnitName])
  , ( FailName
    , opaque
    $ namedPi "T" Retained Type
    $ pure "T"
    )
  ]
  where
    cl = fromMaybe (error "Builtin not closed") . closed
    opaque t = (DataDefinition $ DataDef mempty, cl t)
    dataType t xs = (DataDefinition $ DataDef xs, cl t)
    namedPi :: Name -> Erasability -> TypeE Name -> ExprE Name -> ExprE Name
    namedPi n a t e = Pi (fromName n) a t $ abstract1 n e

convertedContext :: HashMap Name (Converted.Expr Void)
convertedContext = HashMap.fromList $ concat
  [[( TypeName
    , Converted.sized 1
    $ Converted.Lit 1
    )
  , ( IntName
    , Converted.sized 1
    $ Converted.Lit 1
    )
  , ( AddIntName
    , Converted.sized 1
      $ Converted.Lams
        (NonClosureDir Direct)
        (Telescope
        $ Vector.fromList [ (mempty, Direct, slit 1)
                          , (mempty, Direct, slit 1)
                          ])
      $ Scope
      $ Converted.sized 1
      $ Converted.Prim
      $ Primitive Direct
      [TextPart $ "add " <> intT <> " "
      , pure $ Converted.Var $ B 0
      , ", "
      , pure $ Converted.Var $ B 1
      ]
    )
  , ( MaxIntName
    , Converted.sized 1
      $ Converted.Lams
        (NonClosureDir Direct)
        (Telescope
        $ Vector.fromList [ (mempty, Direct, slit 1)
                          , (mempty, Direct, slit 1)
                          ])
      $ Scope
      $ Converted.sized 1
      $ Converted.Let "lt"
      (Converted.sized 1
      $ Converted.Prim
      $ Primitive Direct
      [TextPart $ "icmp ugt " <> intT <> " ", pure $ Converted.Var $ B 0, ", ", pure $ Converted.Var $ B 1])
      $ toScope
      $ Converted.Prim
      $ Primitive Direct
      ["select i1 ", pure $ Converted.Var $ B ()
      , TextPart $ ", " <> intT <> " "
      , pure $ Converted.Var $ F $ B 0
      , TextPart $ ", " <> intT <> " "
      , pure $ Converted.Var $ F $ B 1
      ]
    )
  , ( PrintIntName
    , Converted.sized 1
      $ Converted.Lams
        (NonClosureDir Direct)
        (Telescope
        $ Vector.fromList [(mempty, Direct, slit 1)])
      $ Scope
      $ Converted.sized 1
      $ Converted.Let "res"
      (Converted.sized 1
      $ Converted.Prim
      $ Primitive Direct
      [TextPart $ "call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @size_t-format, i32 0, i32 0), " <> intT <> " "
      , pure $ Converted.Var $ B 0, ")"
      ])
      $ Scope
      $ Converted.Lit 0
    )
  , ( FailName
    , Converted.sized 1
      $ Converted.Lams
        (NonClosureDir Direct)
        (Telescope
        $ Vector.fromList [(mempty, Direct, slit 1)])
      $ Scope
      $ Converted.Sized (Converted.Var $ B 0)
      $ Converted.Prim
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

-- TODO move these
slit :: Literal -> Scope b Converted.Expr v
slit n = Scope $ Converted.Lit n

svarb :: b -> Scope b Converted.Expr a
svarb = Scope . Converted.Var . B

maxArity :: Num n => n
maxArity = 6

deref :: Converted.Expr v -> Converted.Expr v
deref e
  = Converted.Case (Converted.sized 1 e)
  $ ConBranches
  $ pure
    ( Ref
    , Telescope
      $ pure ("dereferenced", (), Scope unknownSize)
    , toScope
    $ Converted.Var $ B 0
    )
  where
    unknownSize = Converted.Global "Builtin.deref.UnknownSize"

apply :: Int -> Converted.Expr Void
apply numArgs
  = Converted.sized 1
  $ Converted.Lams
    (NonClosureDir Indirect)
    (Telescope
    $ Vector.cons ("this", Direct, slit 1)
    $ (\n -> (fromText $ "size" <> shower (unTele n), Direct, slit 1)) <$> Vector.enumFromN 0 numArgs
    <|> (\n -> (fromText $ "x" <> shower (unTele n), Indirect, svarb $ 1 + n)) <$> Vector.enumFromN 0 numArgs)
  $ toScope
  $ Converted.Case (deref $ Converted.Var $ B 0)
  $ ConBranches
  $ pure
    ( Closure
    , Telescope
      $ Vector.fromList [("f_unknown", (), slit 1), ("n", (), slit 1)]
    , toScope
      $ Converted.Case (Converted.sized 1 $ Converted.Var $ B 1)
      $ LitBranches
        [(fromIntegral arity, br arity) | arity <- 1 :| [2..maxArity]]
        $ Converted.Lit 1 -- TODO fail
    )
  where
    br :: Int -> Converted.Expr (Var Tele (Var Tele Void))
    br arity
      | numArgs < arity
        = Converted.Con Ref
        $ pure
        $ Converted.Sized
          (addInts
          $ Vector.cons (Converted.Lit $ fromIntegral $ 3 + numArgs)
          $ (\n -> Converted.Var $ F $ B $ 1 + n) <$> Vector.enumFromN 0 numArgs)
        $ Converted.Con Closure
        $ Vector.cons (Converted.sized 1 $ Converted.Global $ papName (arity - numArgs) numArgs)
        $ Vector.cons (Converted.sized 1 $ Converted.Lit $ fromIntegral $ arity - numArgs)
        $ Vector.cons (Converted.sized 1 $ Converted.Var $ F $ B 0)
        $ (\n -> Converted.sized 1 $ Converted.Var $ F $ B $ 1 + n) <$> Vector.enumFromN 0 numArgs
        <|> (\n -> Converted.Sized (Converted.Var $ F $ B $ 1 + n) $ Converted.Var $ F $ B $ 1 + Tele numArgs + n) <$> Vector.enumFromN 0 numArgs
      | numArgs == arity
        = Converted.Call ClosureDir (Converted.Var $ B 0)
        $ Vector.cons (Converted.sized 1 $ Converted.Var $ F $ B 0, Direct)
        $ (\n -> (Converted.sized 1 $ Converted.Var $ F $ B $ 1 + n, Direct)) <$> Vector.enumFromN 0 numArgs
        <|> (\n -> (Converted.Sized (Converted.Var $ F $ B $ 1 + n) $ Converted.Var $ F $ B $ 1 + Tele numArgs + n, Indirect)) <$> Vector.enumFromN 0 numArgs
      | otherwise
        = Converted.Call (NonClosureDir Indirect) (Converted.Global $ applyName $ numArgs - arity)
        $ Vector.cons
          (Converted.sized 1
          $ Converted.Call ClosureDir (Converted.Var $ B 0)
          $ Vector.cons (Converted.sized 1 $ Converted.Var $ F $ B 0, Direct)
          $ (\n -> (Converted.sized 1 $ Converted.Var $ F $ B $ 1 + n, Direct)) <$> Vector.enumFromN 0 arity
          <|> (\n -> (Converted.Sized (Converted.Var $ F $ B $ 1 + n) $ Converted.Var $ F $ B $ 1 + fromIntegral numArgs + n, Indirect)) <$> Vector.enumFromN 0 arity, Direct)
        $ (\n -> (Converted.sized 1 $ Converted.Var $ F $ B $ 1 + n, Direct)) <$> Vector.enumFromN (fromIntegral arity) (numArgs - arity)
        <|> (\n -> (Converted.Sized (Converted.Var $ F $ B $ 1 + n) $ Converted.Var $ F $ B $ 1 + fromIntegral numArgs + n, Indirect)) <$> Vector.enumFromN (fromIntegral arity) (numArgs - arity)

addInts :: Vector (Converted.Expr v) -> Converted.Expr v
addInts = Vector.foldr1 go
  where
    go x y
      = Converted.Call (NonClosureDir Direct) (Converted.Global AddIntName)
      $ Vector.cons (Converted.Sized (Converted.Lit 1) x, Direct)
      $ pure (Converted.Sized (Converted.Lit 1) y, Direct)

pap :: Int -> Int -> Converted.Expr Void
pap k m
  = Converted.sized 1
  $ Converted.Lams
    ClosureDir
    (Telescope
    $ Vector.cons ("this", Direct, slit 1)
    $ (\n -> (fromText $ "size" <> shower (unTele n), Direct, slit 1)) <$> Vector.enumFromN 0 k
    <|> (\n -> (fromText $ "x" <> shower (unTele n), Indirect, svarb $ 1 + n)) <$> Vector.enumFromN 0 k)
  $ toScope
  $ Converted.Case (deref $ Converted.Var $ B 0)
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
      $ Converted.Call (NonClosureDir Indirect) (Converted.Global $ applyName $ m + k)
      $ Vector.cons (Converted.sized 1 $ Converted.Var $ B 2, Direct)
      $ (\n -> (Converted.sized 1 $ Converted.Var $ B $ 3 + n, Direct)) <$> Vector.enumFromN 0 m
      <|> (\n -> (Converted.sized 1 $ Converted.Var $ F $ B $ 1 + n, Direct)) <$> Vector.enumFromN 0 k
      <|> (\n -> (Converted.Sized (Converted.Var $ B $ 3 + n) $ Converted.Var $ B $ 3 + Tele m + n, Indirect)) <$> Vector.enumFromN 0 m
      <|> (\n -> (Converted.Sized (Converted.Var $ F $ B $ 1 + n) $ Converted.Var $ F $ B $ 1 + Tele k + n, Indirect)) <$> Vector.enumFromN 0 k
    )
