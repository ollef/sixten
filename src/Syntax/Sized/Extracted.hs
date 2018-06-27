{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GADTs, OverloadedStrings, PatternSynonyms, ViewPatterns, TemplateHaskell #-}
module Syntax.Sized.Extracted where

import Control.Monad
import Data.Deriving
import Data.Semigroup
import Data.Text(Text)
import Data.Vector(Vector)

import Syntax hiding (Definition, Module)
import Syntax.Sized.Anno
import TypedFreeVar
import TypeRep(TypeRep)
import Util

data Expr v
  = Var v
  | Global QName
  | Lit Literal
  | Con QConstr (Vector (Anno Expr v)) -- ^ Fully applied
  | Call (Expr v) (Vector (Anno Expr v)) -- ^ Fully applied, only global
  | PrimCall (Maybe Language) RetDir (Expr v) (Vector (Direction, Anno Expr v))
  | Let NameHint (Anno Expr v) (Scope1 Expr v)
  | Case (Anno Expr v) (Branches () Expr v)
  deriving (Foldable, Functor, Traversable)

type Type = Expr

data Declaration = Declaration
  { declName :: Name
  , declRetDir :: RetDir
  , declArgDirs :: Vector Direction
  } deriving (Eq, Ord, Show)

data Submodule contents = Submodule
  { submoduleExternDecls :: [Declaration]
  , submoduleExterns :: [(Language, Text)]
  , submoduleContents :: contents
  } deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

emptySubmodule :: contents -> Submodule contents
emptySubmodule = Submodule mempty mempty

-------------------------------------------------------------------------------
-- Helpers
let_
  :: FreeVar d Expr
  -> Expr (FreeVar d Expr)
  -> Expr (FreeVar d Expr)
  -> Expr (FreeVar d Expr)
let_ v e = Let (varHint v) (Anno e $ varType v) . abstract1 v

pattern MkType :: TypeRep -> Expr v
pattern MkType rep = Lit (TypeRep rep)

typeDir :: Expr v -> Direction
typeDir (MkType rep) = Direct rep
typeDir _ = Indirect

-------------------------------------------------------------------------------
-- Instances
deriveEq1 ''Expr
deriveEq ''Expr
deriveOrd1 ''Expr
deriveOrd ''Expr
deriveShow1 ''Expr
deriveShow ''Expr

instance Applicative Expr where
  pure = Var
  (<*>) = ap

instance Monad Expr where
  return = Var
  expr >>= f = case expr of
    Var v -> f v
    Global v -> Global v
    Lit l -> Lit l
    Con c es -> Con c ((>>>= f) <$> es)
    Call e es -> Call (e >>= f) ((>>>= f) <$> es)
    PrimCall lang retDir e es -> PrimCall lang retDir (e >>= f) (fmap (>>>= f) <$> es)
    Let h e s -> Let h (e >>>= f) (s >>>= f)
    Case e brs -> Case (e >>>= f) (brs >>>= f)

instance GBind Expr where
  global = Global
  gbind f expr = case expr of
    Var _ -> expr
    Global v -> f v
    Lit _ -> expr
    Con c es -> Con c (gbound f <$> es)
    Call e es -> Call (gbind f e) (gbound f <$> es)
    PrimCall lang retDir e es -> PrimCall lang retDir (gbind f e) (fmap (gbound f) <$> es)
    Let h e s -> Let h (gbound f e) (gbound f s)
    Case e brs -> Case (gbound f e) (gbound f brs)

instance v ~ Doc => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Lit l -> prettyM l
    Con c es -> prettyApps (prettyM c) $ prettyM <$> es
    Call e es -> prettyApps (prettyM e) $ prettyM <$> es
    PrimCall lang retDir f es -> "primcall" <+> maybe mempty prettyM lang <+> prettyAnnotation retDir (prettyApps (prettyM f) $ (\(d, e) -> prettyAnnotation d $ prettyM e) <$> es)
    Let h e s -> parens `above` letPrec $ withNameHint h $ \n ->
      "let" <+> prettyM n <+> "=" <+> prettyM e <+> "in" <+>
        prettyM (Util.instantiate1 (pure $ fromName n) s)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+>
      "of" <$$> indent 2 (prettyM brs)

instance Semigroup innards => Semigroup (Submodule innards) where
  Submodule a1 b1 c1 <> Submodule a2 b2 c2
    = Submodule (a1 <> a2) (b1 <> b2) (c1 <> c2)

-- TODO remove Semigroup constraint when ghc has been updated
instance (Monoid innards, Semigroup innards) => Monoid (Submodule innards) where
  mempty = Submodule mempty mempty mempty
  mappend = (<>)
