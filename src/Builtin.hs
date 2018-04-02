{-# LANGUAGE OverloadedStrings, MonadComprehensions #-}
module Builtin where

import Control.Applicative
import Data.Foldable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.List.NonEmpty
import Data.Maybe
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import Backend.Target(Target)
import Builtin.Names
import MonadFresh
import Syntax
import Syntax.Abstract as Abstract
import Syntax.Sized.Anno
import qualified Syntax.Sized.Definition as Sized
import qualified Syntax.Sized.Lifted as Lifted
import TypedFreeVar
import qualified TypeRep
import Util

context :: Target -> HashMap QName (Definition (Expr Void) Void, Type Void Void)
context target = HashMap.fromList
  [ (TypeName, dataType typeRep Type [])
  , (PtrName, dataType
      (Lam mempty Explicit Type $ Scope ptrRep)
      (arrow Explicit Type Type)
      [ ConstrDef RefName $ toScope $ fmap B $ arrow Explicit (pure 0)
        $ Abstract.App (Global PtrName) Explicit (pure 0)
      ])
  , (IntName, opaqueData intRep Type)
  , (NatName, dataType intRep Type
      [ ConstrDef ZeroName $ Scope Nat
      , ConstrDef SuccName $ Scope $ arrow Explicit Nat Nat
      ])
  , (PiTypeName, opaqueData ptrRep Type)
  ]
  where
    cl = fromMaybe (error "Builtin not closed") . closed
    -- TODO: Should be made nonmatchable
    opaqueData rep t = dataType rep t mempty
    dataType rep t xs = (DataDefinition (DataDef xs) rep, cl t)

    intRep = MkType $ TypeRep.intRep target
    ptrRep = MkType $ TypeRep.ptrRep target
    typeRep = MkType $ TypeRep.typeRep target

convertedContext :: Target -> HashMap QName (Sized.Definition Lifted.Expr Void)
convertedContext target = HashMap.fromList $ concat
  [ [(papName left given, pap target left given)
    | given <- [1..maxArity - 1], left <- [1..maxArity - given]
    ]
  , [(applyName arity, apply target arity)
    | arity <- [1..maxArity]
    ]
  ]

convertedSignatures :: Target -> HashMap QName Lifted.FunSignature
convertedSignatures target
  = flip HashMap.mapMaybe (convertedContext target) $ \def ->
    case def of
      Sized.FunctionDef _ _ (Sized.Function tele (AnnoScope _ s)) -> Just (tele, s)
      Sized.ConstantDef _ _ -> Nothing
      Sized.AliasDef -> Nothing

deref :: Lifted.Expr v -> Lifted.Expr v
deref e
  = Lifted.Case (Anno e unknownSize)
  $ ConBranches
  $ pure
  $ ConBranch
    Ref
    (Telescope $ pure $ TeleArg "dereferenced" () $ Scope unknownSize)
    (toScope $ pure $ B 0)
  where
    unknownSize = global "Sixten.Builtin.deref.unknownSize"

maxArity :: Num n => n
maxArity = 6

apply :: Target -> Int -> Sized.Definition Lifted.Expr Void
apply target numArgs = evalFresh $ do
  this <- freeVar "this" () ptrRep
  argTypes <- Vector.forM (Vector.enumFromN 0 numArgs) $ \i ->
    freeVar ("x" <> shower (i :: Int) <> "type") () typeRep
  args <- iforM argTypes $ \i argType ->
    freeVar ("x" <> shower i) () $ pure argType

  let funArgs = pure this <> argTypes <> args
      funAbstr = teleAbstraction funArgs
      funTele = varTelescope funArgs

  funknown <- freeVar "funknown" () piRep
  farity <- freeVar "arity" () intRep

  let clArgs = pure funknown <> pure farity
      clAbstr = teleAbstraction clArgs
      clTele = varTelescope clArgs

      callfunknown argTypes' args' =
        Lifted.PrimCall (ReturnIndirect OutParam) (pure funknown)
        $ Vector.cons (directPtr, varAnno this)
        $ (\v -> (directType, varAnno v)) <$> argTypes'
        <|> (\v -> (Indirect, varAnno v)) <$> args'

      br :: Int -> Lifted.Expr (FreeVar () Lifted.Expr)
      br arity
        | numArgs < arity
          = Lifted.Con Ref
          $ pure
          $ sizedCon target (Lifted.MkType TypeRep.UnitRep) Closure
          $ Vector.cons (Anno (global $ papName (arity - numArgs) numArgs) piRep)
          $ Vector.cons (Anno (Lifted.Lit $ Integer $ fromIntegral $ arity - numArgs) intRep)
          $ varAnno <$> pure this <> argTypes <> args
        | numArgs == arity = callfunknown argTypes args
        | otherwise
          = Lifted.Call (global $ applyName $ numArgs - arity)
          $ Vector.cons
            (flip Anno ptrRep $ callfunknown preArgTypes preArgs)
          $ varAnno <$> postArgTypes <> postArgs
          where
            (preArgTypes, postArgTypes) = Vector.splitAt arity argTypes
            (preArgs, postArgs) = Vector.splitAt arity args

  return
    $ fmap (error "Builtin.apply")
    $ Sized.FunctionDef Public Sized.NonClosure
    $ Sized.Function funTele
    $ abstractAnno funAbstr
    $ flip Anno unknownSize
    $ Lifted.Case (Anno (deref $ pure this) unknownSize)
    $ ConBranches
    $ pure
    $ ConBranch Closure clTele
    $ abstract clAbstr
    $ Lifted.Case (varAnno farity)
    $ LitBranches
      [LitBranch (Integer arity) $ br $ fromIntegral arity | arity <- 1 :| [2..maxArity]]
      (Lifted.Call (global FailName) $ pure $ Anno unitRep typeRep)

  where
    varAnno v = Anno (pure v) (varType v)
    unitRep = Lifted.MkType TypeRep.UnitRep
    intRep = Lifted.MkType $ TypeRep.intRep target
    ptrRep = Lifted.MkType $ TypeRep.ptrRep target
    typeRep = Lifted.MkType $ TypeRep.typeRep target
    piRep = Lifted.MkType $ TypeRep.piRep target
    unknownSize = global "Sixten.Builtin.apply.unknownSize"

    directPtr = Direct $ TypeRep.ptrRep target
    directType = Direct $ TypeRep.typeRep target

pap :: Target -> Int -> Int -> Sized.Definition Lifted.Expr Void
pap target k m = evalFresh $ do
  this <- freeVar "this" () ptrRep
  argTypes <- Vector.forM (Vector.enumFromN 0 k) $ \i ->
    freeVar ("x" <> shower (i :: Int) <> "type") () typeRep
  args <- iforM argTypes $ \i argType ->
    freeVar ("x" <> shower i) () $ pure argType

  let funArgs = pure this <> argTypes <> args
      funAbstr = teleAbstraction funArgs
      funTele = varTelescope funArgs

  unused1 <- freeVar "_" () ptrRep
  unused2 <- freeVar "_" () intRep
  that <- freeVar "that" () ptrRep
  clArgTypes <- Vector.forM (Vector.enumFromN 0 m) $ \i ->
    freeVar ("y" <> shower (i :: Int) <> "type") () typeRep
  clArgs <- iforM clArgTypes $ \i argType ->
    freeVar ("y" <> shower i) () $ pure argType

  let clArgs' = pure unused1 <> pure unused2 <> pure that <> clArgTypes <> clArgs
      clAbstr = teleAbstraction clArgs'
      clTele = varTelescope clArgs'

  return
    $ fmap (error "Builtin.pap")
    $ Sized.FunctionDef Public Sized.NonClosure
    $ Sized.Function funTele
    $ abstractAnno funAbstr
    $ flip Anno unknownSize
    $ Lifted.Case (Anno (deref $ pure this) unknownSize)
    $ ConBranches $ pure $ ConBranch Closure
      clTele
      $ abstract clAbstr
      $ Lifted.Call (global $ applyName $ m + k)
      $ (\v -> Anno (pure v) (varType v)) <$> pure that <> clArgTypes <> argTypes <> clArgs <> args
  where
    unknownSize = global "Sixten.Builtin.pap.unknownSize"
    intRep = Lifted.MkType $ TypeRep.intRep target
    ptrRep = Lifted.MkType $ TypeRep.ptrRep target
    typeRep = Lifted.MkType $ TypeRep.typeRep target

sizedCon :: Target -> Lifted.Expr v -> QConstr -> Vector (Anno Lifted.Expr v) -> Anno Lifted.Expr v
sizedCon target tagRep qc args
  = Anno (Lifted.Con qc args) (productTypes target $ Vector.cons tagRep argTypes)
  where
    argTypes = typeAnno <$> args

productType :: Target -> Lifted.Expr v -> Lifted.Expr v -> Lifted.Expr v
productType _ a (Lifted.MkType TypeRep.UnitRep) = a
productType _ (Lifted.MkType TypeRep.UnitRep) b = b
productType _ (Lifted.MkType rep1) (Lifted.MkType rep2) = Lifted.MkType $ TypeRep.product rep1 rep2
productType target a b
  = Lifted.Call (global ProductTypeRepName)
  $ Vector.fromList [Anno a (Lifted.MkType typeRep), Anno b (Lifted.MkType typeRep)]
  where
     typeRep = TypeRep.typeRep target

productTypes :: Target -> Vector (Lifted.Expr v) -> Lifted.Expr v
productTypes target = foldl' (productType target) (Lifted.MkType TypeRep.UnitRep)
