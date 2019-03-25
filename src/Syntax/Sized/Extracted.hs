{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module Syntax.Sized.Extracted where

import Protolude hiding (Type, TypeRep)

import Data.Deriving
import Data.Hashable.Lifted
import Data.HashMap.Lazy(HashMap)
import Data.Text(Text)
import Data.Vector(Vector)

import Effect
import qualified Effect.Context as Context
import Syntax hiding (Definition)
import Syntax.Sized.Anno
import TypeRep(TypeRep)
import Util

data Expr v
  = Var v
  | Global GName
  | Lit Literal
  | Con QConstr (Vector (Anno Expr v)) -- ^ Fully applied
  | Call (Expr v) (Vector (Anno Expr v)) -- ^ Fully applied, only global
  | PrimCall (Maybe Language) RetDir (Expr v) (Vector (Direction, Anno Expr v))
  | Let NameHint (Anno Expr v) (Scope1 Expr v)
  | Case (Anno Expr v) (Branches Expr v)
  deriving (Foldable, Functor, Traversable, Generic, Generic1, Hashable, Hashable1)

type Type = Expr

data Declaration = Declaration
  { declName :: Name
  , declRetDir :: RetDir
  , declArgDirs :: Vector Direction
  } deriving (Eq, Ord, Show, Generic, Hashable)

data Extracted = Extracted
  { extractedExternDecls :: [Declaration]
  , extractedExterns :: [(Language, Text)]
  , extractedSignatures :: HashMap GName (Signature ReturnIndirect)
  } deriving (Eq, Ord, Show, Generic, Hashable)

-------------------------------------------------------------------------------
-- Helpers
let_
  :: MonadContext (Expr Var) m
  => Var
  -> Expr Var
  -> Expr Var
  -> m (Expr Var)
let_ v e e' = do
  Context.Binding h _ t _ <- Context.lookup v
  return $ Let h (Anno e t) $ abstract1 v e'

pattern MkType :: TypeRep -> Expr v
pattern MkType rep = Lit (TypeRep rep)

typeDir :: Expr v -> Direction
typeDir (MkType rep) = Direct rep
typeDir _ = Indirect

-------------------------------------------------------------------------------
-- Instances
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
    PrimCall lang retDir e es -> PrimCall lang retDir (e >>= f) (fmap (>>>= f) <$> es)
    Let h e s -> Let h (e >>>= f) (s >>>= f)
    Case e brs -> Case (e >>>= f) (brs >>>= f)

instance GBind Expr GName where
  global = Global
  gbind f expr = case expr of
    Var _ -> expr
    Global v -> f v
    Lit _ -> expr
    Con c es -> Con c (gbound f <$> es)
    Call e es -> Call (gbind f e) (gbound f <$> es)
    PrimCall lang retDir e es -> PrimCall lang retDir (gbind f e) (fmap (gbound f) <$> es)
    Let h e s -> Let h (gbound f e) (gbound f s)
    Case e brs -> Case (gbound f e) (gbound f brs)

instance v ~ Doc => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Lit l -> prettyM l
    Con c es -> prettyApps (prettyM c) $ prettyM <$> es
    Call e es -> prettyApps (prettyM e) $ prettyM <$> es
    PrimCall lang retDir f es -> "primcall" <+> maybe mempty prettyM lang <+> prettyAnnotation retDir (prettyApps (prettyM f) $ (\(d, e) -> prettyAnnotation d $ prettyM e) <$> es)
    Let h e s -> parens `above` letPrec $ withNameHint h $ \n ->
      "let" <+> prettyM n <+> "=" <+> prettyM e <+> "in" <+>
        prettyM (Util.instantiate1 (pure $ fromName n) s)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+>
      "of" <$$> Syntax.indent 2 (prettyM brs)

instance Semigroup Extracted where
  Extracted a1 b1 c1 <> Extracted a2 b2 c2
    = Extracted (a1 <> a2) (b1 <> b2) (c1 <> c2)

instance Monoid Extracted where
  mempty = Extracted mempty mempty mempty

deriveEq1 ''Expr
deriveEq ''Expr
deriveOrd1 ''Expr
deriveOrd ''Expr
deriveShow1 ''Expr
deriveShow ''Expr
