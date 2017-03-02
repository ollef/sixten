{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, OverloadedStrings, RankNTypes #-}
module Syntax.Sized.Converted where

import Control.Monad
import Control.Monad.Morph
import Data.Bifunctor
import Data.Monoid
import Data.String
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void
import Prelude.Extras

import Syntax
import qualified Syntax.Sized.Closed as Closed
import Util

data Expr v
  = Var v
  | Global Name
  | Lit Literal
  | Con QConstr (Vector (Expr v)) -- ^ Fully applied
  | Lams ClosureDir (Telescope Direction Type Void) (Scope Tele Expr Void)
  | Call ClosureDir (Expr v) (Vector (Expr v, Direction))
  | Let NameHint (Expr v) (Scope1 Expr v)
  | Case (Expr v) (Branches QConstr () Expr v)
  | Prim (Primitive (Expr v))
  | Anno (Expr v) (Type v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

type Type = Expr

data Signature expr expr' v
  = Function ClosureDir (Telescope Direction expr Void) (Scope Tele expr' Void)
  | Constant Direction (expr' v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

signature :: Expr v -> Signature Expr Closed.Expr v
signature (Lams dir tele s) = Function dir tele (hoist toClosed s)
signature (Anno (Lams dir tele s) _) = Function dir tele (hoist toClosed s)
signature e = Constant (sExprDir e) (toClosed e)

instance MFunctor (Signature expr) where
  hoist f (Function dir tele s)
    = Function dir tele $ hoist f s
  hoist f (Constant d e)
    = Constant d $ f e

-------------------------------------------------------------------------------
-- Helpers
sized :: Literal -> Expr v -> Expr v
sized = flip Anno . Lit

sizeOf :: Expr v -> Expr v
sizeOf (Anno _ sz) = sz
sizeOf _ = error "sizeOf"

sizedSizesOf :: Functor f => f (Expr v) -> f (Expr v)
sizedSizesOf = fmap (sized 1 . sizeOf)

sizeDir :: Expr v -> Direction
sizeDir (Lit 0) = Void
sizeDir (Lit 1) = Direct
sizeDir _ = Indirect

sExprDir :: Expr v -> Direction
sExprDir (Anno _ sz) = sizeDir sz
sExprDir _ = error "sExprDir"

toClosed :: Expr v -> Closed.Expr v
toClosed expr = case expr of
  Var v -> Closed.Var v
  Global v -> Closed.Global v
  Lit l -> Closed.Lit l
  Con qc es -> Closed.Con qc $ toClosed <$> es
  Lams _dir tele s -> Closed.Lams (mapAnnotations (const ()) $ hoist toClosed tele) (hoist toClosed s)
  Call _retDir e es -> Closed.Call (toClosed e) $ toClosed . fst <$> es
  Let h e s -> Closed.Let h (toClosed e) (hoist toClosed s)
  Case e brs -> Closed.Case (toClosed e) $ hoist toClosed brs
  Prim p -> Closed.Prim $ toClosed <$> p
  Anno e t -> Closed.Anno (toClosed e) (toClosed t)

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
  expr >>= f = bind f Global expr

instance GlobalBind Expr where
  global = Global
  bind f g expr = case expr of
    Var v -> f v
    Global v -> g v
    Lit l -> Lit l
    Con c es -> Con c (bind f g <$> es)
    Lams dir tele s -> Lams dir tele s
    Call d e es -> Call d (bind f g e) (first (bind f g) <$> es)
    Let h e s -> Let h (bind f g e) (bound f g s)
    Case e brs -> Case (bind f g e) (bound f g brs)
    Prim p -> Prim $ bind f g <$> p
    Anno e t -> Anno (bind f g e) (bind f g t)

instance (Eq v, IsString v, Pretty v)
      => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Lit l -> prettyM l
    Con c es -> prettyApps (prettyM c) $ prettyM <$> es
    Lams dir tele s -> parens `above` absPrec $
      withTeleHints tele $ \ns ->
        prettyAnnotation dir "\\" <> hsep (map prettyM $ Vector.toList ns) <> "." <+>
          associate absPrec (prettyM $ instantiateTele (pure . fromName) (ns <> pure "?" <> pure "?") $ show <$> s)
    Call d e es ->
        prettyApps (prettyAnnotation d $ prettyM e) $ (\(arg, dir) -> prettyAnnotation dir $ prettyM arg) <$> es
    Let h e s -> parens `above` letPrec $ withNameHint h $ \n ->
      "let" <+> prettyM n <+> "=" <+> prettyM e <+> "in" <+>
        prettyM (Util.instantiate1 (pure $ fromName n) s)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+>
      "of" <$$> indent 2 (prettyM brs)
    Prim p -> prettyM $ pretty <$> p
    Anno e t -> parens `above` annoPrec $
      prettyM e <+> ":" <+> prettyM t
