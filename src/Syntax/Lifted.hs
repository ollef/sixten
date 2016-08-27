{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, OverloadedStrings #-}
module Syntax.Lifted where

import qualified Bound.Scope.Simple as Simple
import Data.Monoid
import Data.String
import qualified Data.Vector as Vector
import Data.Vector(Vector)
import Prelude.Extras

import Syntax
import Util

data SExpr v = Sized (Expr v) (Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Expr v
  = Var v
  | Global Name
  | Lit Literal
  | Con QConstr (Vector (SExpr v)) -- ^ Fully applied
  | Call Direction (Expr v) (Vector (SExpr v, Direction)) -- ^ Fully applied
  | Let NameHint (SExpr v) (Simple.Scope () Expr v)
  | Case (SExpr v) (SimpleBranches QConstr Expr v)
  | Prim (Primitive (Expr v))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Function v
  = Function Direction (Vector (NameHint, Direction)) (Simple.Scope Tele SExpr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Constant v
  = Constant Direction (SExpr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Definition v
  = FunctionDef Visibility (Function v)
  | ConstantDef Visibility (Constant v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-------------------------------------------------------------------------------
-- Helpers
sized :: Literal -> Expr v -> SExpr v
sized = Sized . Lit

sizeOf :: SExpr v -> Expr v
sizeOf (Sized sz _) = sz

-------------------------------------------------------------------------------
-- Instances
instance Eq1 Expr
instance Ord1 Expr
instance Show1 Expr
instance Eq1 SExpr
instance Ord1 SExpr
instance Show1 SExpr

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
        prettyM (instantiate1Var (fromText n) s)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+>
      "of" <$$> indent 2 (prettyM brs)
    Prim p -> prettyM $ pretty <$> p

instance (Eq v, IsString v, Pretty v) => Pretty (SExpr v) where
  prettyM (Sized sz e) = parens `above` annoPrec $
    prettyM e <+> ":" <+> prettyM sz

instance (Eq v, IsString v, Pretty v) => Pretty (Function v) where
  prettyM (Function retDir vs s) = parens `above` absPrec $
    withNameHints (fst <$> vs) $ \ns -> prettyM retDir <+>
      "\\" <> hsep (Vector.toList $ prettyM <$> Vector.zip ns (snd <$> vs)) <> "." <+>
      associate absPrec (prettyM $ instantiateTeleVars (fromText <$> ns) s)

instance (Eq v, IsString v, Pretty v) => Pretty (Constant v) where
  prettyM (Constant dir e) = prettyM dir <+> prettyM e

instance (Eq v, IsString v, Pretty v)
  => Pretty (Syntax.Lifted.Definition v) where
  prettyM (ConstantDef v c) = prettyM v <+> prettyM c
  prettyM (FunctionDef v f) = prettyM v <+> prettyM f
