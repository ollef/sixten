{-# LANGUAGE OverloadedStrings #-}
module Syntax.Concrete.Unscoped where

import Control.Monad
import Data.Bifunctor
import Data.Bitraversable
import Data.List.NonEmpty(NonEmpty)
import Data.Monoid
import Data.String
import Data.Traversable
import Data.Vector(Vector)

import Syntax
import Syntax.Concrete.Pattern

type Con = Either Constr QConstr

data Expr v
  = Var v
  | Lit Literal
  | Pi !Plicitness (Pat (Type v) QName) (Expr v)
  | Lam !Plicitness (Pat (Type v) QName) (Expr v)
  | App (Expr v) !Plicitness (Expr v)
  | Case (Expr v) [(Pat (Expr v) QName, Expr v)]
  | ExternCode (Extern (Expr v))
  | Wildcard
  | SourceLoc !SourceLoc (Type v)
  deriving Show

type Type = Expr

data Definition v
  = Definition Abstract (NonEmpty (Clause v))
  | DataDefinition [(Plicitness, Name, Type v)] [ConstrDef (Expr v)]
  deriving (Show)

data Clause v = Clause (Vector (Plicitness, Pat (Type v) QName)) (Expr v)
  deriving (Show)

-------------------------------------------------------------------------------
-- Smart constructors
pis
  :: [(Plicitness, Pat (Type v) QName)]
  -> Expr v
  -> Expr v
pis ps e = foldr (uncurry Pi) e ps

lams
  :: [(Plicitness, Pat (Type v) QName)]
  -> Expr v
  -> Expr v
lams ps e = foldr (uncurry Lam)  e ps

apps
  :: Expr v
  -> [(Plicitness, Expr v)]
  -> Expr v
apps = foldl (\e1 (p, e2) -> App e1 p e2)

-------------------------------------------------------------------------------
-- Instances
instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  expr >>= f = case expr of
    Var v -> f v
    Lit l -> Lit l
    Pi p pat e -> Pi p (first (>>= f) pat) (e >>= f)
    Lam p pat e -> Lam p (first (>>= f) pat) (e >>= f)
    App e1 p e2 -> App (e1 >>= f) p (e2 >>= f)
    Case e brs -> Case (e >>= f) [(first (>>= f) pat, br >>= f) | (pat, br) <- brs]
    ExternCode c -> ExternCode $ (>>= f) <$> c
    Wildcard -> Wildcard
    SourceLoc loc e -> SourceLoc loc (e >>= f)

instance Functor Expr where fmap = fmapDefault
instance Foldable Expr where foldMap = foldMapDefault
instance Traversable Expr where
  traverse f expr = case expr of
    Var v -> Var <$> f v
    Lit l -> pure $ Lit l
    Pi p pat e -> Pi p <$> bitraverse (traverse f) pure pat <*> traverse f e
    Lam p pat e -> Lam p <$> bitraverse (traverse f) pure pat <*> traverse f e
    App e1 p e2 -> App <$> traverse f e1 <*> pure p <*> traverse f e2
    Case e brs -> Case <$> traverse f e <*> traverse (bitraverse (bitraverse (traverse f) pure) (traverse f)) brs
    ExternCode c -> ExternCode <$> traverse (traverse f) c
    Wildcard -> pure Wildcard
    SourceLoc loc e -> SourceLoc loc <$> traverse f e

instance (Eq v, IsString v, Pretty v) => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Lit l -> prettyM l
    Pi p pat e -> parens `above` absPrec $
        prettyAnnotation p (prettyM pat) <+> "->" <+>
          associate absPrec (prettyM e)
    Lam p pat e -> parens `above` absPrec $
        "\\" <> prettyAnnotation p (prettyM pat) <> "." <+>
          associate absPrec (prettyM e)
    App e1 p e2 -> prettyApp (prettyM e1) (prettyAnnotation p $ prettyM e2)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+> "of" <$$> indent 2 (vcat [prettyM pat <+> "->" <+> prettyM br | (pat, br) <- brs])
    ExternCode c -> prettyM c
    Wildcard -> "_"
    SourceLoc _ e -> prettyM e
