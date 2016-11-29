{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, OverloadedStrings #-}
module Syntax.Lifted where

import Control.Monad
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import qualified Data.Foldable as Foldable
import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import Data.Monoid
import Data.String
import qualified Data.Vector as Vector
import Data.Vector(Vector)
import Data.Void
import Prelude.Extras

import Syntax hiding (Definition, abstractDef)
import TopoSort
import Util

data Expr retDir v
  = Var v
  | Global Name
  | Lit Literal
  | Con QConstr (Vector (Expr retDir v)) -- ^ Fully applied
  | Call retDir (Expr retDir v) (Vector (Expr retDir v, Direction)) -- ^ Fully applied
  | Let NameHint (Expr retDir v) (Scope1 (Expr retDir) v)
  | Case (Expr retDir v) (Branches QConstr () (Expr retDir) v)
  | Prim (Primitive (Expr retDir v))
  | Sized (Expr retDir v) (Expr retDir v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Function retDir expr v
  = Function retDir (Vector (NameHint, Direction)) (Scope Tele expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Constant expr v
  = Constant Direction (expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Definition retDir expr v
  = FunctionDef Visibility (Function retDir expr v)
  | ConstantDef Visibility (Constant expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

dependencyOrder
  :: (GlobalBind expr, Foldable expr)
  => [(Name, Definition retDir expr Void)]
  -> [[(Name, Definition retDir expr Void)]]
dependencyOrder defs = fmap (\n -> (n, m HM.! n)) <$> topoSort (second (bound absurd pure) <$> defs)
  where
    m = HM.fromList defs

-------------------------------------------------------------------------------
-- Helpers
sized :: Literal -> Expr retDir v -> Expr retDir v
sized = Sized . Lit

sizeOf :: Expr retDir v -> Expr retDir v
sizeOf (Sized sz _) = sz
sizeOf _ = error "Lifted.sizeOf"

traverseDefinitionFirst
  :: (Bitraversable expr, Applicative f)
  => (a -> f a')
  -> Definition a (expr a) v
  -> f (Definition a' (expr a') v)
traverseDefinitionFirst f (FunctionDef vis (Function retDir args s))
  = FunctionDef vis <$> (Function <$> f retDir <*> pure args <*> bitraverseScope f pure s)
traverseDefinitionFirst f (ConstantDef vis (Constant dir e))
  = ConstantDef vis <$> (Constant dir <$> bitraverse f pure e)

abstractDef
  :: Monad expr
  => (a -> Maybe b)
  -> Definition retDir expr a
  -> Definition retDir expr (Var b a)
abstractDef f (FunctionDef vis (Function retDir args s))
  = FunctionDef vis
  $ Function retDir args
  $ s >>>= \a -> pure $ maybe (F a) B (f a)
abstractDef f (ConstantDef vis (Constant dir e))
  = ConstantDef vis
  $ Constant dir
  $ fromScope
  $ abstract f e

recursiveAbstractDefs
  :: (Eq v, Monad f, Functor t, Foldable t, Hashable v)
  => t (v, Definition a f v)
  -> t (Definition a f (Var Int v))
recursiveAbstractDefs es = (abstractDef (`HM.lookup` vs) . snd) <$> es
  where
    vs = HM.fromList $ zip (Foldable.toList $ fst <$> es) [(0 :: Int)..]

instantiateDef
  :: Monad expr
  => (b -> expr a)
  -> Definition retDir expr (Var b a)
  -> Definition retDir expr a
instantiateDef f (FunctionDef vis (Function retDir args s))
  = FunctionDef vis
  $ Function retDir args
  $ s >>>= unvar f pure
instantiateDef f (ConstantDef vis (Constant dir e))
  = ConstantDef vis
  $ Constant dir
  $ e >>= unvar f pure

-------------------------------------------------------------------------------
-- Instances
instance Eq retDir => Eq1 (Expr retDir)
instance Ord retDir => Ord1 (Expr retDir)
instance Show retDir => Show1 (Expr retDir)

instance GlobalBind (Expr retDir) where
  global = Global
  bind f g expr = case expr of
    Var v -> f v
    Global v -> g v
    Lit l -> Lit l
    Con c es -> Con c (bind f g <$> es)
    Call retDir e es -> Call retDir (bind f g e) (first (bind f g) <$> es)
    Let h e s -> Let h (bind f g e) (bound f g s)
    Case e brs -> Case (bind f g e) (bound f g brs)
    Prim p -> Prim $ bind f g <$> p
    Sized sz e -> Sized (bind f g sz) (bind f g e)

instance GlobalBound Constant where
  bound f g (Constant dir expr) = Constant dir $ bind f g expr

instance GlobalBound (Function retDir) where
  bound f g (Function retDir args s) = Function retDir args $ bound f g s

instance GlobalBound (Definition retDir) where
  bound f g (FunctionDef vis fdef) = FunctionDef vis $ bound f g fdef
  bound f g (ConstantDef vis cdef) = ConstantDef vis $ bound f g cdef

instance Applicative (Expr retDir) where
  pure = Var
  (<*>) = ap

instance Monad (Expr retDir) where
  expr >>= f = bind f Global expr

instance Bifunctor Expr where
  bimap = bimapDefault

instance Bifoldable Expr where
  bifoldMap = bifoldMapDefault

instance Bitraversable Expr where
  bitraverse f g expr = case expr of
    Var v -> Var <$> g v
    Global v -> pure $ Global v
    Lit l -> pure $ Lit l
    Con c es -> Con c <$> traverse (bitraverse f g) es
    Call retDir e es -> Call <$> f retDir
      <*> bitraverse f g e
      <*> traverse (bitraverse (bitraverse f g) pure) es
    Let h e s -> Let h <$> bitraverse f g e <*> bitraverseScope f g s
    Case e brs -> Case <$> bitraverse f g e <*> bitraverseBranches f g brs
    Prim p -> Prim <$> traverse (bitraverse f g) p
    Sized sz e -> Sized <$> bitraverse f g sz <*> bitraverse f g e

instance (Eq v, IsString v, Pretty v, Eq retDir, Pretty retDir)
  => Pretty (Expr retDir v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Lit l -> prettyM l
    Con c es -> prettyApps (prettyM c) $ prettyM <$> es
    Call retDir e es -> prettyApps (prettyM (e, retDir)) (prettyM <$> es)
    Let h e s -> parens `above` letPrec $ withNameHint h $ \n ->
      "let" <+> prettyM n <+> "=" <+> prettyM e <+> "in" <+>
        prettyM (instantiate1 (pure $ fromName n) s)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+>
      "of" <$$> indent 2 (prettyM brs)
    Prim p -> prettyM $ pretty <$> p
    Sized sz e -> parens `above` annoPrec $
      prettyM e <+> ":" <+> prettyM sz

instance (Eq v, IsString v, Pretty v, Eq retDir, Pretty retDir, Pretty (expr v), Monad expr)
  => Pretty (Function retDir expr v) where
  prettyM (Function retDir vs s) = parens `above` absPrec $
    withNameHints (fst <$> vs) $ \ns -> prettyM retDir <+>
      "\\" <> hsep (Vector.toList $ prettyM <$> Vector.zip ns (snd <$> vs)) <> "." <+>
      associate absPrec (prettyM $ instantiateTele (pure . fromName <$> ns) s)

instance (Eq v, IsString v, Pretty v, Pretty (expr v))
  => Pretty (Constant expr v) where
  prettyM (Constant dir e) = prettyM dir <+> prettyM e

instance (Eq v, IsString v, Pretty v, Eq retDir, Pretty retDir, Pretty (expr v), Monad expr)
  => Pretty (Syntax.Lifted.Definition retDir expr v) where
  prettyM (ConstantDef v c) = prettyM v <+> prettyM c
  prettyM (FunctionDef v f) = prettyM v <+> prettyM f
