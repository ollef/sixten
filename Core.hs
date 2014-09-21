{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Core where

import Bound
import Bound.Var
import Control.Applicative
import Control.Monad
import Data.Bifunctor
import Data.Foldable
import Data.Monoid
import qualified Data.Set as S
import Data.Traversable
import Prelude.Extras

import Pretty
import Util

data Expr v
  = Var v
  | Type -- Int
  | Pi  !(Hint Name) !Plicitness (Expr v) (Scope1 Expr v)
  | Lam !(Hint Name) !Plicitness (Expr v) (Scope1 Expr v)
  | App (Expr v) !Plicitness (Expr v)
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
    Pi  x p t s -> Pi x p (t >>= f) (s >>>= f)
    Lam x p t s -> Lam x p (t >>= f) (s >>>= f)
    App e1 p e2 -> App (e1 >>= f) p (e2 >>= f)

instance Pretty v => Pretty (Expr v) where
  prettyPrec d expr = case expr of
    Var v     -> prettyPrec d v
    Type      -> text "Type"
    Pi x p t (Scope s) -> parensIf (d > absPrec) $
      text "forall" <+> bracesIf (p == Implicit) (px <+> text ":" <+> prettyPrec annoPrec t)
                    <> text "." <+> prettyPrec absPrec (fmap (first $ const px) s)
      where
        px = pretty $ text <$> x
    Lam x p t (Scope s) -> parensIf (d > absPrec) $
      text "\\"     <> bracesIf (p == Implicit) (px <+> text ":" <+> prettyPrec annoPrec t)
                    <> text "." <+> prettyPrec absPrec (fmap (first $ const px) s)
      where
        px = pretty $ text <$> x
    App e1 p e2 -> parensIf (d > appPrec) $
      prettyPrec appPrec e1 <+>
      (if p == Implicit then braces . prettyPrec 0 else prettyPrec (succ appPrec)) e2
    where
      annoPrec = 0
      absPrec  = -1
      appPrec  = 11

etaLam :: Ord v => Hint Name -> Plicitness -> Expr v -> Scope1 Expr v -> Expr v
etaLam _ p _ (Scope (Core.App e p' (Var (B ()))))
  | B () `S.notMember` foldMap S.singleton e && p == p'
    = join $ unvar undefined id <$> e
etaLam n p t s = Core.Lam n p t s

