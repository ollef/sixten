{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, TypeFamilies #-}
module Syntax.Closed where

import qualified Bound.Scope.Simple as Simple
import Data.Monoid
import Data.String
import Data.Vector(Vector)
import Data.Void
import Prelude.Extras

import Meta
import Syntax hiding (lamView)
import Util

data SExpr v = Sized (Expr v) (Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Expr v
  = Var v
  | Global Name
  | Lit Literal
  | Con QConstr (Vector (SExpr v)) -- ^ Fully applied
  | Lams (Telescope Simple.Scope () Expr Void) (Simple.Scope Tele SExpr Void)
  | Call (Expr v) (Vector (SExpr v))
  | Let NameHint (SExpr v) (Simple.Scope () Expr v)
  | Case (SExpr v) (SimpleBranches QConstr Expr v)
  | Prim (Primitive (Expr v))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-------------------------------------------------------------------------------
-- Smart constructors
apps :: Expr v -> Vector (SExpr v) -> Expr v
apps (Call e es1) es2 = Call e $ es1 <> es2
apps e es = Call e es

-------------------------------------------------------------------------------
-- Helpers
sized :: Literal -> Expr v -> SExpr v
sized = Sized . Lit

sizeOf :: SExpr v -> Expr v
sizeOf (Sized sz _) = sz

sizedSizesOf :: Functor f => f (SExpr v) -> f (SExpr v)
sizedSizesOf = fmap (sized 1 . sizeOf)

sizeDir :: Expr v -> Direction
sizeDir (Lit 0) = Void
sizeDir (Lit 1) = Direct
sizeDir _ = Indirect

sExprDir :: SExpr v -> Direction
sExprDir (Sized sz _) = sizeDir sz

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
    Lams tele s -> parens `above` absPrec $
      withTeleHints tele $ \ns ->
        "\\" <> prettySimpleTeleVarTypes ns (show <$> tele) <> "." <+>
        associate absPrec (prettyM $ instantiateTeleVars (fromText <$> ns) $ show <$> s)
    Call e es -> parens `above` annoPrec $
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

instance MetaVary Expr (MetaVar Expr) where
  type MetaData Expr (MetaVar Expr) = ()
  refineVar v _ = return $ Var v
