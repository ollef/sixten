{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Input where

import Bound
import Control.Applicative
import Control.Monad
import Data.Bifunctor
import Data.Foldable
import Data.Monoid
import Data.Traversable
import Prelude.Extras

import Util
import Pretty

data Def v = Def v (Expr v)

data Expr v
  = Var v
  | Type                             -- ^ Type : Type
  | Pi  Name !Plicitness (Scope1 Expr v) -- ^ Dependent function space
  | Lam Name !Plicitness (Scope1 Expr v)
  | App (Expr v) !Plicitness (Expr v)
  | Anno (Expr v) (Expr v)
  | Wildcard                         -- ^ Attempt to infer it
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Eq1 Expr; instance Ord1 Expr; instance Show1 Expr

instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  expr >>= f = case expr of
    Var v       -> f v
    Type        -> Type
    Pi  n p s   -> Pi n p (s >>>= f)
    Lam n p s   -> Lam n p (s >>>= f)
    App e1 p e2 -> App (e1 >>= f) p (e2 >>= f)
    Anno e t    -> Anno (e >>= f) (t >>= f)
    Wildcard    -> Wildcard

instance Pretty v => Pretty (Expr v) where
  prettyPrec d expr = case expr of
    Var v     -> prettyPrec d v
    Type      -> text "Type"
    Pi  x p (Scope s) -> parensIf (d > absPrec) $
      text "forall" <+> bracesIf (p == Implicit) (text x) <> text "."
                    <+> prettyPrec absPrec (fmap (first $ const (text x)) s)
    Lam x  p(Scope s) -> parensIf (d > absPrec) $
      text "\\"     <> bracesIf (p == Implicit) (text x) <> text "."
                    <+> prettyPrec absPrec (fmap (first $ const (text x)) s)
    App e1 p e2 -> parensIf (d > appPrec) $
      prettyPrec appPrec e1 <+>
      (if p == Implicit then braces . prettyPrec 0 else prettyPrec (succ appPrec)) e2
    Anno e t  -> parensIf (d > annoPrec) $
      prettyPrec annoPrec e <+> text ":" <+> prettyPrec annoPrec t
    Wildcard  -> text "_"
    where
      annoPrec = 0
      absPrec  = -1
      appPrec  = 11
