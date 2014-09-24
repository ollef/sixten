{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Input where

import Bound
import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Monoid
import Data.String
import Data.Traversable
import Prelude.Extras

import Util
import Pretty

data Def v = Def v (Expr v)

data Expr v
  = Var v
  | Type                             -- ^ Type : Type
  | Pi  !(Hint (Maybe Name)) !Plicitness (Scope1 Expr v) -- ^ Dependent function space
  | Lam !(Hint (Maybe Name)) !Plicitness (Scope1 Expr v)
  | App (Expr v) !Plicitness (Expr v)
  | Anno (Expr v) (Expr v)
  | Wildcard                         -- ^ Attempt to infer it
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-------------------------------------------------------------------------------
-- Instances
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

instance (IsString v, Pretty v) => Pretty (Expr v) where
  prettyPrec expr = case expr of
    Var v     -> prettyPrec v
    Type      -> pure $ text "Type"
    Pi  h p s -> withHint h $ \x -> parens `above` absPrec $ do
      v <- inviolable $ bracesWhen (p == Implicit) $ pure $ text x
      b <- associate  $ prettyPrec $ instantiate1 (return $ fromString x) s
      return $ text "forall" <+> v <> text "." <+> b
    Lam h p s -> withHint h $ \x -> parens `above` absPrec $ do
      v <- inviolable $ bracesWhen (p == Implicit) $ pure $ text x
      b <- associate  $ prettyPrec $ instantiate1 (return $ fromString x) s
      return $ text "\\" <+> v <> text "." <+> b
    App e1 p e2 -> prettyApp (prettyPrec e1) (bracesWhen (p == Implicit) $ prettyPrec e2)
    Anno e t  -> parens `above` annoPrec $ do
      x <- prettyPrec e
      y <- associate $ prettyPrec t
      return $ x <+> text ":" <+> y
    Wildcard  -> pure $ text "_"
