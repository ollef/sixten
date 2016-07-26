{-# LANGUAGE OverloadedStrings, ViewPatterns, PatternSynonyms #-}
module Builtin where

import qualified Bound.Scope.Simple as Simple
import Control.Applicative
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HM
import Data.Maybe
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import Syntax
import Syntax.Abstract as Abstract
import qualified Syntax.Converted as Converted
import Util

pattern SizeName <- ((==) "Size" -> True) where SizeName = "Size"
pattern Size = Global SizeName

pattern AddSizeName <- ((==) "addSize" -> True) where AddSizeName = "addSize"
pattern AddSize e1 e2 = App (App (Global AddSizeName) ReEx e1) ReEx e2

pattern PrintSizeName <- ((==) "printSize" -> True) where PrintSizeName = "printSize"
pattern PrintSize e1 = App (Global AddSizeName) ReEx e1

pattern MaxSizeName <- ((==) "maxSize" -> True) where MaxSizeName = "maxSize"
pattern MaxSize e1 e2 = App (App (Global MaxSizeName) ReEx e1) ReEx e2

pattern TypeName <- ((==) "Type" -> True) where TypeName = "Type"
pattern Type sz = App (Global TypeName) IrIm sz

pattern RefName <- ((==) "Ref" -> True) where RefName = "Ref"
pattern PtrName <- ((==) "Ptr" -> True) where PtrName = "Ptr"

pattern Closure <- ((== QConstr "Builtin" "CL") -> True) where Closure = QConstr "Builtin" "CL"

pattern Ref <- ((== QConstr PtrName RefName) -> True) where Ref = QConstr PtrName RefName

applyName :: Int -> Name
applyName n = "apply_" <> shower n

papName :: Int -> Int -> Name
papName k m = "pap_" <> shower k <> "_" <> shower m

context :: Program Expr Void
context = HM.fromList
  [ (SizeName, opaque $ Type $ Lit 1)
  , (AddSizeName, opaque $ arrow ReEx Size $ arrow ReEx Size Size)
  , (MaxSizeName, opaque $ arrow ReEx Size $ arrow ReEx Size Size)
  , (PrintSizeName, opaque $ arrow ReEx Size Size)
  , (TypeName, opaque $ arrow IrIm Size $ Type $ Lit 0)
  , (PtrName, dataType (Abstract.pi_ "size" IrIm Size
                       $ arrow IrEx (Type $ pure "size")
                       $ Type $ Lit 1)
                       [ ConstrDef RefName $ toScope $ fmap B $ arrow ReEx (pure 1)
                                           $ apps (Global PtrName) [(IrIm, pure 0), (IrEx, pure 1)]
                       ])
  ]
  where
    cl = fromMaybe (error "Builtin not closed") . closed
    opaque t = (DataDefinition $ DataDef mempty, cl t)
    dataType t xs = (DataDefinition $ DataDef xs, cl t)

convertedContext :: HashMap Name (Converted.SExpr Void)
convertedContext = HM.fromList $ concat
  [[ ( AddSizeName
    , Converted.sized 1
      $ Converted.Lams
        Direct
        (Telescope
        $ Vector.fromList [ (mempty, Direct, slit 1)
                          , (mempty, Direct, slit 1)
                          ])
      $ Simple.Scope
      $ Converted.sized 1
      $ Converted.Prim
      $ "add i64 " <> pure (Converted.Var $ B 0) <> ", " <> pure (Converted.Var $ B 1)
    )
  , ( MaxSizeName
    , Converted.sized 1
      $ Converted.Lams
        Direct
        (Telescope
        $ Vector.fromList [ (mempty, Direct, slit 1)
                          , (mempty, Direct, slit 1)
                          ])
      $ Simple.Scope
      $ Converted.sized 1
      $ Converted.Let "lt"
      (Converted.sized 1
      $ Converted.Prim
      $ "icmp ult i64 " <> pure (Converted.Var $ B 0) <> ", " <> pure (Converted.Var $ B 1))
      $ Simple.Scope
      $ Converted.Prim
      $ "select i1 " <> pure (Converted.Var $ B ())
      <> ", i64 " <> pure (Converted.Var $ F $ B 0) <> ", i64 "
      <> pure (Converted.Var $ F $ B 1)
    )
  , ( PrintSizeName
    , Converted.sized 1
      $ Converted.Lams
        Direct
        (Telescope
        $ Vector.fromList [(mempty, Direct, slit 1)])
      $ Simple.Scope
      $ Converted.sized 1
      $ Converted.Let "res"
      (Converted.sized 1
      $ Converted.Prim
      ("call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @i64-format, i64 0, i64 0), i64 " <> pure (Converted.Var $ B 0) <> ")"))

      $ Simple.Scope
      $ Converted.Prim
      $ "zext i32 " <> pure (Converted.Var $ B ()) <> " to i64"
    )
  ]
  , [(papName left given, pap left given) | given <- [1..maxArity - 1], left <- [1..maxArity - given]]
  , [(applyName arity, apply arity) | arity <- [1..maxArity]]
  ]

-- TODO move these
slit :: Literal -> Simple.Scope b Converted.Expr v
slit n = Simple.Scope $ Converted.Lit n

svarb :: b -> Simple.Scope b Converted.Expr a
svarb = Simple.Scope . Converted.Var . B

maxArity :: Num n => n
maxArity = 3

deref :: Converted.Expr v -> Converted.Expr v
deref e
  = Converted.Case (Converted.sized 1 e)
  $ SimpleConBranches
  [ ( Ref
    , Telescope
      $ pure ("dereferenced", (), Simple.Scope $ Converted.Global "Builtin.deref.UnknownSize")
    , Simple.Scope
    $ Converted.Var $ B 0
    )
  ]

apply :: Int -> Converted.SExpr Void
apply numArgs
  = Converted.sized 1
  $ Converted.Lams
    Indirect
    (Telescope
    $ Vector.cons ("this", Direct, slit 1)
    $ (\n -> (fromText $ "size" <> shower (unTele n), Direct, slit 1)) <$> Vector.enumFromN 0 numArgs
    <|> (\n -> (fromText $ "x" <> shower (unTele n), Indirect, svarb $ 1 + n)) <$> Vector.enumFromN 0 numArgs)
  $ Simple.Scope
  $ unknownSize
  $ Converted.Case (unknownSize $ deref $ Converted.Var $ B 0)
  $ SimpleConBranches
  [ ( Closure
    , Telescope
      $ Vector.fromList [("f_unknown", (), slit 1), ("n", (), slit 1)]
    , Simple.Scope
      $ Converted.Case (Converted.sized 1 $ Converted.Var $ B 1)
      $ SimpleLitBranches
        [(fromIntegral arity, br arity) | arity <- [1..maxArity]]
        $ Converted.Lit 1 -- TODO fail
    )
  ]
  where
    unknownSize = Converted.Sized $ Converted.Global "Builtin.apply.UnknownSize"
    br :: Int -> Converted.Expr (Var Tele (Var Tele Void))
    br arity
      | numArgs < arity
        = Converted.Con Ref
        $ pure
        $ Converted.Sized
          (addSizes
          $ Vector.cons (Converted.Lit $ fromIntegral $ 3 + numArgs)
          $ (\n -> Converted.Var $ F $ B $ 1 + n) <$> Vector.enumFromN 0 numArgs)
        $ Converted.Con Closure
        $ Vector.cons (Converted.sized 1 $ Converted.Global $ papName (arity - numArgs) numArgs)
        $ Vector.cons (Converted.sized 1 $ Converted.Lit $ fromIntegral $ arity - numArgs)
        $ Vector.cons (Converted.sized 1 $ Converted.Var $ F $ B 0)
        $ (\n -> Converted.Sized (Converted.Var $ F $ B $ 1 + n) $ Converted.Var $ F $ B $ 1 + Tele numArgs + n) <$> Vector.enumFromN 0 numArgs
      | numArgs == arity
        = Converted.Call Indirect (Converted.Var $ B 0)
        $ Vector.cons (Converted.sized 1 $ Converted.Var $ F $ B 0, Direct)
        $ (\n -> (Converted.sized 1 $ Converted.Var $ F $ B $ 1 + n, Direct)) <$> Vector.enumFromN 0 numArgs
        <|> (\n -> (Converted.Sized (Converted.Var $ F $ B $ 1 + n) $ Converted.Var $ F $ B $ 1 + Tele numArgs + n, Indirect)) <$> Vector.enumFromN 0 numArgs
      | otherwise
        = Converted.Call Indirect (Converted.Global $ applyName $ numArgs - arity)
        $ Vector.cons
          (Converted.sized 1
          $ Converted.Call Indirect (Converted.Var $ B 0)
          $ Vector.cons (Converted.sized 1 $ Converted.Var $ F $ B 0, Direct)
          $ (\n -> (Converted.sized 1 $ Converted.Var $ F $ B $ 1 + n, Direct)) <$> Vector.enumFromN 0 arity
          <|> (\n -> (Converted.Sized (Converted.Var $ F $ B $ 1 + n) $ Converted.Var $ F $ B $ 1 + fromIntegral numArgs + n, Indirect)) <$> Vector.enumFromN 0 arity, Direct)
        $ (\n -> (Converted.sized 1 $ Converted.Var $ F $ B $ 1 + n, Direct)) <$> Vector.enumFromN (fromIntegral arity) (numArgs - arity)
        <|> (\n -> (Converted.Sized (Converted.Var $ F $ B $ 1 + n) $ Converted.Var $ F $ B $ 1 + fromIntegral numArgs + n, Indirect)) <$> Vector.enumFromN (fromIntegral arity) (numArgs - arity)

addSizes :: Vector (Converted.Expr v) -> Converted.Expr v
addSizes = Vector.foldr1 go
  where
    go x y
      = Converted.Call Direct (Converted.Global AddSizeName)
      $ Vector.cons (Converted.Sized (Converted.Lit 1) x, Direct)
      $ pure (Converted.Sized (Converted.Lit 1) y, Direct)

pap :: Int -> Int -> Converted.SExpr Void
pap k m
  = unknownSize
  $ Converted.Lams
    Indirect
    (Telescope
    $ Vector.cons ("this", Direct, slit 1)
    $ (\n -> (fromText $ "size" <> shower (unTele n), Direct, slit 1)) <$> Vector.enumFromN 0 k
    <|> (\n -> (fromText $ "x" <> shower (unTele n), Indirect, svarb $ 1 + n)) <$> Vector.enumFromN 0 k)
  $ Simple.Scope
  $ unknownSize
  $ Converted.Case (unknownSize $ deref $ Converted.Var $ B 0)
  $ SimpleConBranches
    [ ( Closure
      , Telescope
        $ Vector.cons ("_", (), slit 1)
        $ Vector.cons ("_", (), slit 1)
        $ Vector.cons ("that", (), slit 1)
        $ (\n -> (fromText $ "size" <> shower (unTele n), (), slit 1)) <$> Vector.enumFromN 0 m
        <|> (\n -> (fromText $ "y" <> shower (unTele n), (), svarb $ 3 + n)) <$> Vector.enumFromN 0 m
      , Simple.Scope
        $ Converted.Call Indirect (Converted.Global $ applyName $ m + k)
        $ Vector.cons (Converted.sized 1 $ Converted.Var $ B 2, Direct)
        $ (\n -> (Converted.sized 1 $ Converted.Var $ B $ 3 + n, Direct)) <$> Vector.enumFromN 0 m
        <|> (\n -> (Converted.sized 1 $ Converted.Var $ F $ B $ 1 + n, Direct)) <$> Vector.enumFromN 0 k
        <|> (\n -> (Converted.Sized (Converted.Var $ B $ 3 + n) $ Converted.Var $ B $ 3 + Tele m + n, Indirect)) <$> Vector.enumFromN 0 m
        <|> (\n -> (Converted.Sized (Converted.Var $ F $ B $ 1 + n) $ Converted.Var $ F $ B $ 1 + Tele k + n, Indirect)) <$> Vector.enumFromN 0 k
      )
    ]
  where
    unknownSize = Converted.Sized $ Converted.Global "Builtin.pap.UnknownSize"
