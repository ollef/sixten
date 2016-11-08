{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, OverloadedStrings, RankNTypes #-}
module Syntax.Converted where

import Control.Monad
import Data.Bifunctor
import Data.Monoid
import Data.String
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void
import Prelude.Extras

import Syntax
import Util

data Expr v
  = Var v
  | Global Name
  | Lit Literal
  | Con QConstr (Vector (Expr v)) -- ^ Fully applied
  | Lams (Maybe Direction) (Telescope Direction Expr Void) (Scope Tele Expr Void)
  | Call (Maybe Direction) (Expr v) (Vector (Expr v, Direction))
  | Let NameHint (Expr v) (Scope1 Expr v)
  | Case (Expr v) (Branches QConstr () Expr v)
  | Prim (Primitive (Expr v))
  | Sized (Expr v) (Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Signature expr expr' v
  = Function (Maybe Direction) (Telescope Direction expr Void) (Scope Tele expr' Void)
  | Constant Direction (expr' v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

signature :: Expr v -> Signature Expr Expr v
signature (Lams dir tele s) = Function dir tele s
signature (Sized _ (Lams dir tele s)) = Function dir tele s
signature e = Constant (sExprDir e) e

hoistSignature
  :: (Monad expr1, Monad expr2)
  => (forall v'. expr1 v' -> expr2 v')
  -> Signature expr expr1 v
  -> Signature expr expr2 v
hoistSignature f (Function dir tele s)
  = Function dir tele $ toScope $ f $ fromScope s
hoistSignature f (Constant d e)
  = Constant d $ f e

-------------------------------------------------------------------------------
-- Helpers
sized :: Literal -> Expr v -> Expr v
sized = Sized . Lit

sizeOf :: Expr v -> Expr v
sizeOf (Sized sz _) = sz
sizeOf _ = error "sizeOf"

sizedSizesOf :: Functor f => f (Expr v) -> f (Expr v)
sizedSizesOf = fmap (sized 1 . sizeOf)

sizeDir :: Expr v -> Direction
sizeDir (Lit 0) = Void
sizeDir (Lit 1) = Direct
sizeDir _ = Indirect

sExprDir :: Expr v -> Direction
sExprDir (Sized sz _) = sizeDir sz
sExprDir _ = error "sExprDir"

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
    Global g -> Global g
    Lit l -> Lit l
    Con c es -> Con c ((>>= f) <$> es)
    Lams dir tele s -> Lams dir tele s
    Call d e es -> Call d (e >>= f) (first (>>= f) <$> es)
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
    Lams dir tele s -> parens `above` absPrec $
      withTeleHints tele $ \ns ->
        prettyM dir <+> "\\" <> hsep (map prettyM $ Vector.toList ns) <> "." <+>
          associate absPrec (prettyM $ instantiateTele (pure . fromName <$> ns) $ show <$> s)
    Call d e es ->
      prettyApp (brackets $ prettyM d) $ prettyApps (prettyM e) (prettyM <$> es)
    Let h e s -> parens `above` letPrec $ withNameHint h $ \n ->
      "let" <+> prettyM n <+> "=" <+> prettyM e <+> "in" <+>
        prettyM (instantiate1 (pure $ fromName n) s)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+>
      "of" <$$> indent 2 (prettyM brs)
    Prim p -> prettyM $ pretty <$> p
    Sized sz e -> parens `above` annoPrec $
      prettyM e <+> ":" <+> prettyM sz
