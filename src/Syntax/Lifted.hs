{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, OverloadedStrings #-}
module Syntax.Lifted where

import qualified Bound.Scope.Simple as Simple
import Data.String
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
  = FunctionDef (Function v)
  | ConstantDef (Constant v)
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
