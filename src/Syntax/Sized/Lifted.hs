{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module Syntax.Sized.Lifted where

import Protolude hiding (Type, TypeRep)

import Data.Deriving
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import FreeVar
import Syntax hiding (Definition)
import Syntax.Sized.Anno
import qualified TypedFreeVar as Typed
import TypeRep(TypeRep)
import Util

data Expr v
  = Var v
  | Global GName
  | Lit Literal
  | Con QConstr (Vector (Anno Expr v)) -- ^ Fully applied
  | Call (Expr v) (Vector (Anno Expr v)) -- ^ Fully applied, only global
  | PrimCall RetDir (Expr v) (Vector (Direction, Anno Expr v))
  | Let NameHint (Anno Expr v) (Scope1 Expr v)
  | Case (Anno Expr v) (Branches Expr v)
  | ExternCode (Extern (Anno Expr v)) (Type v)
  deriving (Foldable, Functor, Traversable)

type Type = Expr

type FunSignature = (Closed (Telescope Type), Closed (Scope TeleVar Type))

-------------------------------------------------------------------------------
-- Helpers

letTyped
  :: Typed.FreeVar Expr
  -> Expr (Typed.FreeVar Expr)
  -> Expr (Typed.FreeVar Expr)
  -> Expr (Typed.FreeVar Expr)
letTyped v e = Let (Typed.varHint v) (Anno e $ Typed.varType v) . abstract1 v

let_
  :: FreeVar d
  -> Anno Expr (FreeVar d)
  -> Expr (FreeVar d)
  -> Expr (FreeVar d)
let_ v e = Let (varHint v) e . abstract1 v

pattern MkType :: TypeRep -> Expr v
pattern MkType rep = Lit (TypeRep rep)

typeDir :: Expr v -> Direction
typeDir (MkType rep) = Direct rep
typeDir _ = Indirect

callsView :: Expr v -> Maybe (Expr v, Vector (Anno Expr v))
callsView (Call expr exprs) = Just $ go expr [exprs]
  where
    go (Call e es) ess = go e (es : ess)
    go e ess = (e, Vector.concat ess)
callsView _ = Nothing

-------------------------------------------------------------------------------
-- Instances
deriveEq1 ''Expr
deriveEq ''Expr
deriveOrd1 ''Expr
deriveOrd ''Expr
deriveShow1 ''Expr
deriveShow ''Expr

instance Applicative Expr where
  pure = Var
  (<*>) = ap

instance Monad Expr where
  return = Var
  expr >>= f = case expr of
    Var v -> f v
    Global v -> Global v
    Lit l -> Lit l
    Con c es -> Con c ((>>>= f) <$> es)
    Call e es -> Call (e >>= f) ((>>>= f) <$> es)
    PrimCall retDir e es -> PrimCall retDir (e >>= f) (fmap (>>>= f) <$> es)
    Let h e s -> Let h (e >>>= f) (s >>>= f)
    Case e brs -> Case (e >>>= f) (brs >>>= f)
    ExternCode c retType -> ExternCode ((>>>= f) <$> c) (retType >>= f)

instance GBind Expr GName where
  global = Global
  gbind f expr = case expr of
    Var _ -> expr
    Global v -> f v
    Lit _ -> expr
    Con c es -> Con c (gbound f <$> es)
    Call e es -> Call (gbind f e) (gbound f <$> es)
    PrimCall retDir e es -> PrimCall retDir (gbind f e) (fmap (gbound f) <$> es)
    Let h e s -> Let h (gbound f e) (gbound f s)
    Case e brs -> Case (gbound f e) (gbound f brs)
    ExternCode c retType -> ExternCode (gbound f <$> c) (gbind f retType)

instance v ~ Doc => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Lit l -> prettyM l
    Con c es -> prettyApps (prettyM c) $ prettyM <$> es
    Call e es -> prettyApps (prettyM e) $ prettyM <$> es
    PrimCall retDir f es -> "primcall" <+> prettyAnnotation retDir (prettyApps (prettyM f) $ (\(d, e) -> prettyAnnotation d $ prettyM e) <$> es)
    Let h (Anno e t) s -> parens `above` letPrec $ withNameHint h $ \n ->
      "let" <+> prettyM n <+> ":" <+> prettyM t <+> "=" <+> prettyM e <+> "in" <+>
        prettyM (Util.instantiate1 (pure $ fromName n) s)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+>
      "of" <$$> indent 2 (prettyM brs)
    ExternCode c retType ->
      parens `above` annoPrec $ prettyM c <+> ":" <+> prettyM retType
