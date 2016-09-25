{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, FlexibleInstances, OverloadedStrings, ViewPatterns #-}
module Syntax.SLambda where

import qualified Bound.Scope.Simple as Simple
import Data.Monoid
import Data.String
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Prelude.Extras

import Syntax hiding (lamView)
import Util

data SExpr v = Sized (Expr v) (Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Expr v
  = Var v
  | Global Name
  | Lit Literal
  | Con QConstr (Vector (SExpr v)) -- ^ Fully applied
  | Lam !NameHint (Expr v) (Simple.Scope () SExpr v)
  | App (Expr v) (SExpr v)
  | Case (SExpr v) (SimpleBranches QConstr Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

appsView :: Expr v -> (Expr v, Vector (SExpr v))
appsView = go []
  where
    go args (App e1 se2) = go (se2:args) e1
    go args e = (e, Vector.fromList args)

lamView :: SExpr v -> Maybe (NameHint, (), Expr v, Simple.Scope () SExpr v)
lamView (Sized _ (Lam h e s)) = Just (h, (), e, s)
lamView _ = Nothing

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
    Con c es -> prettyApps (prettyM c) $ prettyM <$> es
    Lit l -> prettyM l
    (simpleBindingsViewM lamView . Sized (Global "pretty-impossible") -> Just (tele, s)) -> parens `above` absPrec $
      withTeleHints tele $ \ns ->
        "\\" <> prettySimpleTeleVarTypes ns tele <> "." <+>
        associate absPrec (prettyM $ instantiateTeleVars (fromText <$> ns) s)
    Lam {} -> error "impossible prettyPrec lam"
    App e1 e2 -> parens `above` annoPrec $
      prettyApp (prettyM e1) (prettyM e2)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+>
      "of" <$$> indent 2 (prettyM brs)

instance (Eq v, IsString v, Pretty v) => Pretty (SExpr v) where
  prettyM (Sized sz e) = parens `above` annoPrec $
    prettyM e <+> ":" <+> prettyM sz
