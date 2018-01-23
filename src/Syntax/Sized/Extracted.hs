{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GADTs, OverloadedStrings, PatternSynonyms, ViewPatterns, TemplateHaskell #-}
module Syntax.Sized.Extracted where

import Control.Monad
import Data.Deriving
import Data.Monoid
import Data.Text(Text)
import Data.Vector(Vector)

import Syntax hiding (Definition, Module)
import TypeRep(TypeRep)
import Util

data Expr v
  = Var v
  | Global QName
  | Lit Literal
  | Con QConstr (Vector (Expr v)) -- ^ Fully applied
  | Call (Expr v) (Vector (Expr v)) -- ^ Fully applied, only global
  | PrimCall (Maybe Language) RetDir (Expr v) (Vector (Direction, Expr v))
  | Let NameHint (Expr v) (Scope1 Expr v)
  | Case (Expr v) (Branches () Expr v)
  | Anno (Expr v) (Type v)
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
pattern Sized :: Type v -> Expr v -> Expr v
pattern Sized sz e = Anno e sz

pattern MkType :: TypeRep -> Expr v
pattern MkType rep <- (ignoreAnno -> Lit (TypeRep rep))
  where MkType rep = Lit (TypeRep rep)

ignoreAnno :: Expr v -> Expr v
ignoreAnno (Anno e _) = ignoreAnno e
ignoreAnno e = e

typeOf :: Expr v -> Expr v
typeOf (Anno _ rep) = rep
typeOf _ = error "Extracted.typeOf"

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

instance GlobalBind Expr where
  global = Global
  bind f g expr = case expr of
    Var v -> f v
    Global v -> g v
    Lit l -> Lit l
    Con c es -> Con c (bind f g <$> es)
    Call e es -> Call (bind f g e) (bind f g <$> es)
    PrimCall lang retDir e es -> PrimCall lang retDir (bind f g e) (fmap (bind f g) <$> es)
    Let h e s -> Let h (bind f g e) (bound f g s)
    Case e brs -> Case (bind f g e) (bound f g brs)
    Anno e t -> Anno (bind f g e) (bind f g t)

instance Applicative Expr where
  pure = Var
  (<*>) = ap

instance Monad Expr where
  expr >>= f = bind f Global expr

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
    Anno e t -> parens `above` annoPrec $
      prettyM e <+> ":" <+> prettyM t

instance Monoid innards => Monoid (Submodule innards) where
  mempty = Submodule mempty mempty mempty
  Submodule a1 b1 c1 `mappend` Submodule a2 b2 c2
    = Submodule (a1 <> a2) (b1 <> b2) (c1 <> c2)
