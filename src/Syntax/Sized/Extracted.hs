{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, OverloadedStrings, PatternSynonyms #-}
module Syntax.Sized.Extracted where

import Control.Monad
import Data.Bifunctor
import Data.Monoid
import Data.String
import Data.Vector(Vector)
import Prelude.Extras
import Data.Text(Text)

import Syntax hiding (Definition)
import Util

data Expr v
  = Var v
  | Global Name
  | Lit Literal
  | Con QConstr (Vector (Expr v)) -- ^ Fully applied
  | Call (Expr v) (Vector (Expr v)) -- ^ Fully applied, only global
  | PrimCall RetDir (Expr v) (Vector (Expr v, Direction))
  | Let NameHint (Expr v) (Scope1 Expr v)
  | Case (Expr v) (Branches QConstr () Expr v)
  | Prim (Primitive (Expr v))
  | Anno (Expr v) (Type v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

type Type = Expr

data Declaration = Declaration
  { declName :: Name
  , declRetDir :: ReturnDirection ReturnIndirect
  , declArgDirs :: Vector Direction
  } deriving (Eq, Ord, Show)

data Module innards = Module
  { moduleDecls :: [Declaration]
  , moduleExterns :: [(Language, Text)]
  , moduleInnards :: innards
  } deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-------------------------------------------------------------------------------
-- Helpers
pattern Sized sz e = Anno e sz

sizeOf :: Expr v -> Expr v
sizeOf (Anno _ sz) = sz
sizeOf _ = error "Extracted.sizeOf"

sizeDir :: Expr v -> Direction
sizeDir (Lit (Integer n)) = Direct n
sizeDir _ = Indirect

-------------------------------------------------------------------------------
-- Instances
instance Eq1 Expr
instance Ord1 Expr
instance Show1 Expr

instance GlobalBind Expr where
  global = Global
  bind f g expr = case expr of
    Var v -> f v
    Global v -> g v
    Lit l -> Lit l
    Con c es -> Con c (bind f g <$> es)
    Call e es -> Call (bind f g e) (bind f g <$> es)
    PrimCall retDir e es -> PrimCall retDir (bind f g e) (first (bind f g) <$> es)
    Let h e s -> Let h (bind f g e) (bound f g s)
    Case e brs -> Case (bind f g e) (bound f g brs)
    Prim p -> Prim $ bind f g <$> p
    Anno e t -> Anno (bind f g e) (bind f g t)

instance Applicative Expr where
  pure = Var
  (<*>) = ap

instance Monad Expr where
  expr >>= f = bind f Global expr

instance (Eq v, IsString v, Pretty v)
  => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Lit l -> prettyM l
    Con c es -> prettyApps (prettyM c) $ prettyM <$> es
    Call e es -> prettyApps (prettyM e) $ prettyM <$> es
    PrimCall retDir f es -> "primcall" <+> prettyAnnotation retDir (prettyApps (prettyM f) $ (\(e, d) -> prettyAnnotation d $ prettyM e) <$> es)
    Let h e s -> parens `above` letPrec $ withNameHint h $ \n ->
      "let" <+> prettyM n <+> "=" <+> prettyM e <+> "in" <+>
        prettyM (Util.instantiate1 (pure $ fromName n) s)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+>
      "of" <$$> indent 2 (prettyM brs)
    Prim p -> prettyM $ pretty <$> p
    Anno e t -> parens `above` annoPrec $
      prettyM e <+> ":" <+> prettyM t

instance Monoid innards => Monoid (Module innards) where
  mempty = Module mempty mempty mempty
  Module a1 b1 c1 `mappend` Module a2 b2 c2
    = Module (a1 <> a2) (b1 <> b2) (c1 <> c2)
