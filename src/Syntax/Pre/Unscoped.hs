{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
module Syntax.Pre.Unscoped where

import Protolude hiding (Type)

import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty(NonEmpty)
import Data.Vector(Vector)

import Syntax hiding (Definition)
import qualified Syntax.Pre.Literal as Pre

data Expr
  = Var PreName
  | Lit Pre.Literal
  | Pi !Plicitness (Pat PreName Pre.Literal PreName Type) Expr
  | Lam !Plicitness (Pat PreName Pre.Literal PreName Type) Expr
  | App Expr !Plicitness Expr
  | Let (Vector (SourceLoc, ConstantDef Expr)) Expr
  | Case Expr [(SourceLoc, Pat PreName Pre.Literal PreName Type, Expr)]
  | ExternCode (Extern Expr)
  | Wildcard
  | SourceLoc !SourceLoc Type
  | Error Error
  deriving (Show, Generic, Hashable)

type Type = Expr

data ConstantDef e
  = ConstantDef Name Abstract (NonEmpty (Clause e)) (Maybe e)
  deriving (Show, Generic, Hashable)

definitionName :: ConstantDef e -> Name
definitionName (ConstantDef n _ _ _) = n

data ADTOrGADTConstrDef typ
  = ADTConstrDef Constr [typ]
  | GADTConstrDef Constr typ
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable, Generic, Hashable)

constrName :: ADTOrGADTConstrDef typ -> Constr
constrName (ADTConstrDef c _) = c
constrName (GADTConstrDef c _) = c

data Definition
  = ConstantDefinition (ConstantDef Expr)
  | DataDefinition !Boxiness Name [(Plicitness, Name, Type)] [ADTOrGADTConstrDef Expr]
  | ClassDefinition Name [(Plicitness, Name, Type)] [Method Expr]
  | InstanceDefinition Type [(SourceLoc, ConstantDef Expr)]
  deriving (Show, Generic, Hashable)

data Clause e
  = Clause !SourceLoc !(Vector (Plicitness, Pat PreName Pre.Literal PreName e)) e
  deriving (Show, Generic, Hashable)

-------------------------------------------------------------------------------
-- Smart constructors
pis
  :: [(Plicitness, Pat PreName Pre.Literal PreName Type)]
  -> Expr
  -> Expr
pis ps e = foldr (uncurry Pi) e ps

lams
  :: [(Plicitness, Pat PreName Pre.Literal PreName Type)]
  -> Expr
  -> Expr
lams ps e = foldr (uncurry Lam)  e ps

apps
  :: Expr
  -> [(Plicitness, Expr)]
  -> Expr
apps = foldl (\e1 (p, e2) -> App e1 p e2)

-------------------------------------------------------------------------------
-- Instances
instance Pretty Expr where
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
    Let ds e -> parens `above` letPrec $
      "let" <+> align (vcat ((\(_, d) -> prettyM d) <$> ds)) <$$> "in" <+> prettyM e
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+> "of" <$$> indent 2 (vcat [prettyM pat <+> "->" <+> prettyM br | (_, pat, br) <- brs])
    ExternCode c -> prettyM c
    Wildcard -> "_"
    SourceLoc _ e -> prettyM e
    Syntax.Pre.Unscoped.Error e -> prettyM e

instance Pretty e => Pretty (ConstantDef e) where
  prettyM (ConstantDef name a cls Nothing)
    = prettyM a <$$> vcat (prettyNamed (prettyM name) <$> cls)
  prettyM (ConstantDef name a cls (Just typ))
    = prettyM a <$$> vcat (NonEmpty.cons (prettyM name <+> ":" <+> prettyM typ) (prettyNamed (prettyM name) <$> cls))

instance (Pretty e) => PrettyNamed (Clause e) where
  prettyNamed name (Clause _ pats body) = name <+> hcat ((\(p, pat) -> prettyAnnotation p (prettyM pat)) <$> pats) <+> "=" <+> prettyM body
