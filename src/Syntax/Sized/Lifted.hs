{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, MonadComprehensions, OverloadedStrings #-}
module Syntax.Sized.Lifted where

import Control.Monad
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import qualified Data.HashMap.Lazy as HashMap
import Data.Monoid
import Data.String
import Data.Vector(Vector)
import Data.Void
import Prelude.Extras

import Syntax hiding (Definition)
import TopoSort
import Util
import qualified Syntax.Sized.Closed as Closed
import qualified Syntax.Sized.Converted as Converted

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
  = Function retDir (Telescope Direction expr v) (Scope Tele expr v)
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
dependencyOrder defs = fmap (\n -> (n, m HashMap.! n)) <$> topoSort (second (bound absurd pure) <$> defs)
  where
    m = HashMap.fromList defs

-------------------------------------------------------------------------------
-- Helpers
sized :: Literal -> Expr retDir v -> Expr retDir v
sized = Sized . Lit

sizeOf :: Expr retDir v -> Expr retDir v
sizeOf (Sized sz _) = sz
sizeOf _ = error "Lifted.sizeOf"

bitraverseDefinition
  :: (Bitraversable expr, Applicative f)
  => (a -> f a')
  -> (b -> f b')
  -> Definition a (expr a) b
  -> f (Definition a' (expr a') b')
bitraverseDefinition f g (FunctionDef vis (Function retDir args s))
  = FunctionDef vis <$> (Function <$> f retDir <*> bitraverseTelescope f g args <*> bitraverseScope f g s)
bitraverseDefinition f g (ConstantDef vis (Constant dir e))
  = ConstantDef vis <$> (Constant dir <$> bitraverse f g e)

toClosed :: Expr retDir v -> Closed.Expr v
toClosed expr = case expr of
  Var v -> Closed.Var v
  Global v -> Closed.Global v
  Lit l -> Closed.Lit l
  Con qc es -> Closed.Con qc $ toClosed <$> es
  Call _retDir e es -> Closed.Call (toClosed e) $ toClosed . fst <$> es
  Let h e s -> Closed.Let h (toClosed e) (hoistScope toClosed s)
  Case e brs -> Closed.Case (toClosed e) $ hoistBranches toClosed brs
  Prim p -> Closed.Prim $ toClosed <$> p
  Sized sz e -> Closed.Sized (toClosed sz) (toClosed e)

toConverted :: Expr ClosureDir v -> Converted.Expr v
toConverted expr = case expr of
  Var v -> Converted.Var v
  Global v -> Converted.Global v
  Lit l -> Converted.Lit l
  Con qc es -> Converted.Con qc $ toConverted <$> es
  Call retDir e es -> Converted.Call retDir (toConverted e) $ first toConverted <$> es
  Let h e s -> Converted.Let h (toConverted e) (hoistScope toConverted s)
  Case e brs -> Converted.Case (toConverted e) $ hoistBranches toConverted brs
  Prim p -> Converted.Prim $ toConverted <$> p
  Sized sz e -> Converted.Sized (toConverted sz) (toConverted e)

signature
  :: Function ClosureDir (Expr ClosureDir) Void
  -> Converted.Signature Converted.Expr Closed.Expr Void
signature (Function retDir tele bodyScope)
  = Converted.Function
    retDir
    (hoistTelescope toConverted tele)
    (hoistScope toClosed bodyScope)

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
  bound f g (Function retDir args s) = Function retDir (bound f g args) $ bound f g s

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
        prettyM (Util.instantiate1 (pure $ fromName n) s)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+>
      "of" <$$> indent 2 (prettyM brs)
    Prim p -> prettyM $ pretty <$> p
    Sized sz e -> parens `above` annoPrec $
      prettyM e <+> ":" <+> prettyM sz

instance (Eq v, IsString v, Pretty v, Eq retDir, Pretty retDir, Pretty (expr v), Monad expr)
  => Pretty (Function retDir expr v) where
  prettyM (Function retDir vs s) = parens `above` absPrec $
    withNameHints (teleNames vs) $ \ns -> prettyM retDir <+>
      "\\" <> prettyTeleVars ns vs <> "." <+>
      associate absPrec (prettyM $ instantiateTele (pure . fromName) ns s)

instance (Eq v, IsString v, Pretty v, Pretty (expr v))
  => Pretty (Constant expr v) where
  prettyM (Constant dir e) = prettyM dir <+> prettyM e

instance (Eq v, IsString v, Pretty v, Eq retDir, Pretty retDir, Pretty (expr v), Monad expr)
  => Pretty (Syntax.Sized.Lifted.Definition retDir expr v) where
  prettyM (ConstantDef v c) = prettyM v <+> prettyM c
  prettyM (FunctionDef v f) = prettyM v <+> prettyM f
