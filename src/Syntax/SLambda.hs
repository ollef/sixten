{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, FlexibleInstances, OverloadedStrings, ViewPatterns #-}
module Syntax.SLambda where

import Control.Monad
import Data.Monoid
import Data.String
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Prelude.Extras

import Syntax hiding (lamView)
import Util

data Expr v
  = Var v
  | Global Name
  | Lit Literal
  | Con QConstr (Vector (Expr v)) -- ^ Fully applied
  | Lam !NameHint (Expr v) (Scope1 Expr v)
  | App (Expr v) (Expr v)
  | Case (Expr v) (Branches QConstr () Expr v)
  | Sized (Expr v) (Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

appsView :: Expr v -> (Expr v, Vector (Expr v))
appsView = go []
  where
    go args (App e1 e2) = go (e2:args) e1
    go args e = (e, Vector.fromList args)

lamView :: Expr v -> Maybe (NameHint, (), Expr v, Scope () Expr v)
lamView (Sized _ e) = lamView e
lamView (Lam h e s) = Just (h, (), e, s)
lamView _ = Nothing

-------------------------------------------------------------------------------
-- Instances
instance Eq1 Expr
instance Ord1 Expr
instance Show1 Expr

instance Applicative Expr where
  pure = Var
  (<*>) = ap

instance Monad Expr where
  return = Var
  expr >>= f = case expr of
    Var v -> f v
    Global n -> Global n
    Lit l -> Lit l
    Con qc es -> Con qc ((>>= f) <$> es)
    Lam h e s -> Lam h (e >>= f) (s >>>= f)
    App e1 e2 -> App (e1 >>= f) (e2 >>= f)
    Case e brs -> Case (e >>= f) (brs >>>= f)
    Sized sz e -> Sized (sz >>= f) (e >>= f)

instance (Eq v, IsString v, Pretty v)
      => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Con c es -> prettyApps (prettyM c) $ prettyM <$> es
    Lit l -> prettyM l
    App e1 e2 -> parens `above` annoPrec $
      prettyApp (prettyM e1) (prettyM e2)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+>
      "of" <$$> indent 2 (prettyM brs)
    Sized sz e -> parens `above` annoPrec $
      prettyM e <+> ":" <+> prettyM sz
    (bindingsViewM lamView -> Just (tele, s)) -> parens `above` absPrec $
      withTeleHints tele $ \ns ->
        "\\" <> prettyTeleVarTypes ns tele <> "." <+>
        associate absPrec (prettyM $ instantiateTele (pure . fromText <$> ns) s)
    Lam {} -> error "impossible prettyPrec lam"
