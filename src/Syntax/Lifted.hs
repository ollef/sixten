{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, OverloadedStrings #-}
module Syntax.Lifted where

import Control.Monad
import Data.Bifunctor
import Data.Monoid
import Data.String
import qualified Data.Vector as Vector
import Data.Vector(Vector)
import Prelude.Extras

import Syntax
import Util

data Expr v
  = Var v
  | Global Name
  | Lit Literal
  | Con QConstr (Vector (Expr v)) -- ^ Fully applied
  | Call Direction (Expr v) (Vector (Expr v, Direction)) -- ^ Fully applied
  | Let NameHint (Expr v) (Scope1 Expr v)
  | Case (Expr v) (Branches QConstr () Expr v)
  | Prim (Primitive (Expr v))
  | Sized (Expr v) (Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Function v
  = Function Direction (Vector (NameHint, Direction)) (Scope Tele Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Constant v
  = Constant Direction (Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Definition v
  = FunctionDef Visibility (Function v)
  | ConstantDef Visibility (Constant v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-------------------------------------------------------------------------------
-- Helpers
sized :: Literal -> Expr v -> Expr v
sized = Sized . Lit

sizeOf :: Expr v -> Expr v
sizeOf (Sized sz _) = sz
sizeOf _ = error "Lifted.sizeOf"

-------------------------------------------------------------------------------
-- Instances
instance Eq1 Expr
instance Ord1 Expr
instance Show1 Expr

instance Applicative Expr where
  pure = Var
  (<*>) = ap

instance Monad Expr where
  expr >>= f = case expr of
    Var v -> f v
    Global g -> Global g
    Lit l -> Lit l
    Con c es -> Con c ((>>= f) <$> es)
    Call retDir e es -> Call retDir (e >>= f) (first (>>= f) <$> es)
    Let h e s -> Let h (e >>= f) (s >>>= f)
    Case e brs -> Case (e >>= f) (brs >>>= f)
    Prim p -> Prim $ (>>= f) <$> p
    Sized sz e -> Sized (sz >>= f) (e >>= f)

instance (Eq v, IsString v, Pretty v)
  => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Lit l -> prettyM l
    Con c es -> prettyApps (prettyM c) $ prettyM <$> es
    Call _retDir e es -> parens `above` annoPrec $ -- TODO dir
      prettyApps (prettyM e) (prettyM <$> es)
    Let h e s -> parens `above` letPrec $ withNameHint h $ \n ->
      "let" <+> prettyM n <+> "=" <+> prettyM e <+> "in" <+>
        prettyM (instantiate1 (pure $ fromText n) s)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+>
      "of" <$$> indent 2 (prettyM brs)
    Prim p -> prettyM $ pretty <$> p
    Sized sz e -> parens `above` annoPrec $
      prettyM e <+> ":" <+> prettyM sz

instance (Eq v, IsString v, Pretty v) => Pretty (Function v) where
  prettyM (Function retDir vs s) = parens `above` absPrec $
    withNameHints (fst <$> vs) $ \ns -> prettyM retDir <+>
      "\\" <> hsep (Vector.toList $ prettyM <$> Vector.zip ns (snd <$> vs)) <> "." <+>
      associate absPrec (prettyM $ instantiateTele (pure . fromText <$> ns) s)

instance (Eq v, IsString v, Pretty v) => Pretty (Constant v) where
  prettyM (Constant dir e) = prettyM dir <+> prettyM e

instance (Eq v, IsString v, Pretty v)
  => Pretty (Syntax.Lifted.Definition v) where
  prettyM (ConstantDef v c) = prettyM v <+> prettyM c
  prettyM (FunctionDef v f) = prettyM v <+> prettyM f
