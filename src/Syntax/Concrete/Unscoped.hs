{-# LANGUAGE OverloadedStrings #-}
module Syntax.Concrete.Unscoped where

import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty(NonEmpty)
import Data.Monoid
import Data.Vector(Vector)

import Syntax hiding (Definition)
import Syntax.Concrete.Pattern

type Con = Either Constr QConstr

data Expr
  = Var QName
  | Lit Literal
  | Pi !Plicitness (Pat Type QName) Expr
  | Lam !Plicitness (Pat Type QName) Expr
  | App Expr !Plicitness Expr
  | Let (Vector (SourceLoc, Definition Expr)) Expr
  | Case Expr [(Pat Expr QName, Expr)]
  | ExternCode (Extern Expr)
  | Wildcard
  | SourceLoc !SourceLoc Type
  deriving Show

type Type = Expr

data Definition e
  = Definition Name Abstract (NonEmpty (Clause e)) (Maybe e)
  deriving (Show)

definitionName :: Definition e -> Name
definitionName (Definition n _ _ _) = n

data TopLevelDefinition
  = TopLevelDefinition (Definition Expr)
  | TopLevelDataDefinition Name [(Plicitness, Name, Type)] [ConstrDef Expr]
  | TopLevelClassDefinition Name [(Plicitness, Name, Type)] [MethodDef Expr]
  | TopLevelInstanceDefinition Type [(SourceLoc, Definition Expr)]
  deriving (Show)

data Clause e = Clause (Vector (Plicitness, Pat e QName)) e
  deriving (Show)

-------------------------------------------------------------------------------
-- Smart constructors
pis
  :: [(Plicitness, Pat Type QName)]
  -> Expr
  -> Expr
pis ps e = foldr (uncurry Pi) e ps

lams
  :: [(Plicitness, Pat Type QName)]
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
      "case" <+> inviolable (prettyM e) <+> "of" <$$> indent 2 (vcat [prettyM pat <+> "->" <+> prettyM br | (pat, br) <- brs])
    ExternCode c -> prettyM c
    Wildcard -> "_"
    SourceLoc _ e -> prettyM e

instance Pretty e => Pretty (Definition e) where
  prettyM (Definition name a cls Nothing)
    = prettyM a <$$> vcat (prettyNamed (prettyM name) <$> cls)
  prettyM (Definition name a cls (Just typ))
    = prettyM a <$$> vcat (NonEmpty.cons (prettyM name <+> ":" <+> prettyM typ) (prettyNamed (prettyM name) <$> cls))

instance (Pretty e) => PrettyNamed (Clause e) where
  prettyNamed name (Clause pats body) = name <+> hcat ((\(p, pat) -> prettyAnnotation p (prettyM pat)) <$> pats) <+> "=" <+> prettyM body
