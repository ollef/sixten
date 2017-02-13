{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, TypeFamilies #-}
module Syntax.Sized.Closed where

import Control.Monad
import Data.Monoid
import Data.String
import Data.Vector(Vector)
import Data.Void
import Prelude.Extras

import Syntax hiding (lamView)
import Util

data Expr v
  = Var v
  | Global Name
  | Lit Literal
  | Con QConstr (Vector (Expr v)) -- ^ Fully applied
  | Lams (Telescope () Expr Void) (Scope Tele Expr Void)
  | Call (Expr v) (Vector (Expr v))
  | Let NameHint (Expr v) (Scope1 Expr v)
  | Case (Expr v) (Branches QConstr () Expr v)
  | Prim (Primitive (Expr v))
  | Sized (Expr v) (Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-------------------------------------------------------------------------------
-- Smart constructors
apps :: Expr v -> Vector (Expr v) -> Expr v
apps (Call e es1) es2 = Call e $ es1 <> es2
apps e es = Call e es

-------------------------------------------------------------------------------
-- Helpers
sized :: Literal -> Expr v -> Expr v
sized = Sized . Lit

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
  return = pure
  expr >>= f = bind f Global expr

instance GlobalBind Expr where
  global = Global
  bind f g expr = case expr of
    Var v -> f v
    Global v -> g v
    Con c es -> Con c (bind f g <$> es)
    Lit l -> Lit l
    Lams tele s -> Lams tele s
    Call e es -> Call (bind f g e) (bind f g <$> es)
    Let h e s -> Let h (bind f g e) (bound f g s)
    Case e brs -> Case (bind f g e) (bound f g brs)
    Prim p -> Prim (bind f g <$> p)
    Sized sz e -> Sized (bind f g sz) (bind f g e)

instance (Eq v, IsString v, Pretty v)
      => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Con c es -> prettyApps (prettyM c) $ prettyM <$> es
    Lit l -> prettyM l
    Lams tele s -> parens `above` absPrec $
      withTeleHints tele $ \ns ->
        "\\" <> prettyTeleVarTypes ns (show <$> tele) <> "." <+>
        associate absPrec (prettyM $ instantiateTele (pure . fromName) ns $ show <$> s)
    Call e es -> parens `above` annoPrec $
      prettyApps (prettyM e) (prettyM <$> es)
    Let h e s -> parens `above` letPrec $ withNameHint h $ \n ->
      "let" <+> prettyM n <+> "=" <+> prettyM e <+> "in" <+>
        prettyM (Util.instantiate1 (pure $ fromName n) s)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+>
      "of" <$$> indent 2 (prettyM brs)
    Prim p -> prettyM $ pretty <$> p
    Sized sz e -> parens `above` annoPrec $
      prettyM e <+> ":" <+> prettyM sz
