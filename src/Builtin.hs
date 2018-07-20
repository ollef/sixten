{-# LANGUAGE MonadComprehensions, OverloadedStrings, ViewPatterns #-}
module Builtin where

import Control.Applicative
import Data.Foldable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.List.NonEmpty
import Data.Maybe
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Backend.Target(Target)
import Builtin.Names
import MonadFresh
import Syntax
import Syntax.Core as Core
import Syntax.Sized.Anno
import qualified Syntax.Sized.Definition as Sized
import qualified Syntax.Sized.Lifted as Lifted
import TypedFreeVar
import qualified TypeRep
import Util

context :: Target -> HashMap QName (ClosedDefinition Expr, Biclosed Type)
context target = HashMap.fromList
  [ (TypeName, dataType typeRep Type [])
  , (PtrName, dataType
      (Lam mempty Explicit Type $ Scope ptrRep)
      (arrow Explicit Type Type)
      [ ConstrDef RefName $ toScope $ fmap B $ arrow Explicit (pure 0)
        $ Core.App (Global PtrName) Explicit (pure 0)
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
    dataType rep typ xs = (closeDefinition id id $ DataDefinition (DataDef (piTelescope cltyp) xs) rep, biclose id id $ cltyp)
      where
        cltyp = cl typ

    intRep = MkType $ TypeRep.intRep target
    ptrRep = MkType $ TypeRep.ptrRep target
    typeRep = MkType $ TypeRep.typeRep target

convertedContext :: Target -> HashMap QName (Closed (Sized.Definition Lifted.Expr))
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
    case open def of
      Sized.FunctionDef _ _ (Sized.Function tele (AnnoScope _ s)) -> Just (close id tele, close id s)
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

apply :: Target -> Int -> Closed (Sized.Definition Lifted.Expr)
apply target numArgs = evalFresh $ do
  this <- freeVar "this" () ptrRep
  argTypes <- Vector.forM (Vector.enumFromN 0 numArgs) $ \i ->
    freeVar ("x" <> shower (i :: Int) <> "type") () typeRep
  args <- iforM argTypes $ \i argType ->
    freeVar ("x" <> shower i) () $ pure argType

  funknown <- freeVar "funknown" () piRep
  farity <- freeVar "arity" () intRep

  let funArgs = pure this <> argTypes <> args
      clArgs = pure funknown <> pure farity

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
    $ close (error "Builtin.apply")
    $ Sized.FunctionDef Public Sized.NonClosure
    $ Sized.functionTyped funArgs
    $ flip Anno unknownSize
    $ Lifted.Case (Anno (deref $ pure this) unknownSize)
    $ ConBranches $ pure
    $ conBranchTyped Closure clArgs
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

pap :: Target -> Int -> Int -> Closed (Sized.Definition Lifted.Expr)
pap target k m = evalFresh $ do
  this <- freeVar "this" () ptrRep
  argTypes <- Vector.forM (Vector.enumFromN 0 k) $ \i ->
    freeVar ("x" <> shower (i :: Int) <> "type") () typeRep
  args <- iforM argTypes $ \i argType ->
    freeVar ("x" <> shower i) () $ pure argType

  unused1 <- freeVar "_" () ptrRep
  unused2 <- freeVar "_" () intRep
  that <- freeVar "that" () ptrRep
  clArgTypes <- Vector.forM (Vector.enumFromN 0 m) $ \i ->
    freeVar ("y" <> shower (i :: Int) <> "type") () typeRep
  clArgs <- iforM clArgTypes $ \i argType ->
    freeVar ("y" <> shower i) () $ pure argType

  let funArgs = pure this <> argTypes <> args
      clArgs' = pure unused1 <> pure unused2 <> pure that <> clArgTypes <> clArgs

  return
    $ close (error "Builtin.pap")
    $ Sized.FunctionDef Public Sized.NonClosure
    $ Sized.functionTyped funArgs
    $ flip Anno unknownSize
    $ Lifted.Case (Anno (deref $ pure this) unknownSize)
    $ ConBranches $ pure
    $ conBranchTyped Closure clArgs'
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
