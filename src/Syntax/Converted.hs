{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, OverloadedStrings, RankNTypes #-}
module Syntax.Converted where

import qualified Bound.Scope.Simple as Simple
import Data.Monoid
import Data.String
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void
import Prelude.Extras

import Syntax
import Syntax.Primitive
import Util

data SExpr v = Sized (Expr v) (Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Expr v
  = Var v
  | Global Name
  | Lit Literal
  | Con QConstr (Vector (SExpr v)) -- ^ Fully applied
  | Lams Direction (Telescope Simple.Scope Direction Expr Void) (Simple.Scope Tele SExpr Void)
  | Call Direction (Expr v) (Vector (SExpr v, Direction))
  | Let NameHint (SExpr v) (Simple.Scope () Expr v)
  | Case (SExpr v) (SimpleBranches QConstr Expr v)
  | Prim (Primitive (Expr v))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Signature expr v
  = Function Direction (Telescope Simple.Scope Direction Expr Void) (Simple.Scope Tele expr Void)
  | Constant (expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

signature :: SExpr v -> Signature SExpr v
signature (Sized _ (Lams retDir tele s)) = Function retDir tele s
signature e = Constant e

mapSignature
  :: (forall v'. expr v' -> expr' v')
  -> Signature expr v
  -> Signature expr' v
mapSignature f (Function d tele (Simple.Scope e)) = Function d tele $ Simple.Scope $ f e
mapSignature f (Constant e) = Constant $ f e

-------------------------------------------------------------------------------
-- Helpers
sized :: Literal -> Expr v -> SExpr v
sized = Sized . Lit

sizeOf :: SExpr v -> Expr v
sizeOf (Sized sz _) = sz

sizedSizesOf :: Functor f => f (SExpr v) -> f (SExpr v)
sizedSizesOf = fmap (sized 1 . sizeOf)

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
    Lams d tele s -> parens `above` absPrec $
      withTeleHints tele $ \ns ->
        prettyM d <+> "\\" <> hsep (map prettyM $ Vector.toList ns) <> "." <+>
          associate absPrec (prettyM $ instantiateVar (fromText . (ns Vector.!) . unTele) $ show <$> s)
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
