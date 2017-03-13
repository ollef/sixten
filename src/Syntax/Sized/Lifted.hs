{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, MonadComprehensions, OverloadedStrings #-}
module Syntax.Sized.Lifted where

import Control.Monad
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HashMap
import Data.Monoid
import Data.String
import Data.Vector(Vector)
import Data.Void
import Prelude.Extras

import Syntax hiding (Definition)
import TopoSort
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

data Function expr v
  = Function (Telescope () expr v) (Scope Tele expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Constant expr v
  = Constant (expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data IsClosure
  = NonClosure
  | IsClosure
  deriving (Eq, Ord, Show)

data Definition expr v
  = FunctionDef Visibility IsClosure (Function expr v)
  | ConstantDef Visibility (Constant expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

dependencyOrder
  :: (GlobalBind expr, Foldable expr)
  => [(Name, Definition expr Void)]
  -> [[(Name, Definition expr Void)]]
dependencyOrder defs = fmap (\n -> (n, m HashMap.! n)) <$> topoSort (second (bound absurd pure) <$> defs)
  where
    m = HashMap.fromList defs

-------------------------------------------------------------------------------
-- Helpers
sized :: Literal -> Expr v -> Expr v
sized = flip Anno . Lit

sizeOf :: Expr v -> Expr v
sizeOf (Anno _ sz) = sz
sizeOf _ = error "Lifted.sizeOf"

sizeDir :: Expr v -> Direction
sizeDir (Lit 0) = Void
sizeDir (Lit 1) = Direct
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

instance GlobalBound Constant where
  bound f g (Constant expr) = Constant $ bind f g expr

instance GlobalBound Function where
  bound f g (Function args s) = Function (bound f g args) $ bound f g s

instance GlobalBound Definition where
  bound f g (FunctionDef vis cl fdef) = FunctionDef vis cl $ bound f g fdef
  bound f g (ConstantDef vis cdef) = ConstantDef vis $ bound f g cdef

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

instance (Eq v, IsString v, Pretty v, Pretty (expr v), Monad expr)
  => Pretty (Function expr v) where
  prettyM (Function vs s) = parens `above` absPrec $
    withNameHints (teleNames vs) $ \ns ->
      "\\" <> prettyTeleVars ns vs <> "." <+>
      associate absPrec (prettyM $ instantiateTele (pure . fromName) ns s)

instance PrettyAnnotation IsClosure where
  prettyAnnotation IsClosure = prettyTightApp "[]"
  prettyAnnotation NonClosure = id

instance (Eq v, IsString v, Pretty v, Pretty (expr v))
  => Pretty (Constant expr v) where
  prettyM (Constant e) = prettyM e

instance (Eq v, IsString v, Pretty v, Pretty (expr v), Monad expr)
  => Pretty (Syntax.Sized.Lifted.Definition expr v) where
  prettyM (ConstantDef v c) = prettyM v <+> prettyM c
  prettyM (FunctionDef v cl f) = prettyM v <+> prettyAnnotation cl (prettyM f)
