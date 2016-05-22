{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, OverloadedStrings #-}
module Syntax.Concrete where

import Control.Monad
import qualified Data.Foldable as Foldable
import Data.Monoid
import Data.String
import Prelude.Extras

import Syntax
import Util

data Expr v
  = Var v
  | Global Name -- ^ Really just a variable, but it's often annoying to not have it
  | Lit Literal
  | Con (Either Constr QConstr)
  | Pi  !NameHint !Annotation (Type v) (Scope1 Expr v)  -- ^ Dependent function space
  | Lam !NameHint !Annotation (Scope1 Expr v)
  | App (Expr v) !Annotation (Expr v)
  | Case (Expr v) (Branches (Either Constr QConstr) Expr v)
  | Anno (Expr v) (Expr v)
  | Wildcard  -- ^ Attempt to infer it
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-- | Synonym for documentation purposes
type Type = Expr

-- * Smart constructors
tlam :: NameHint -> Annotation -> Maybe (Type v) -> Scope1 Expr v -> Expr v
tlam x p Nothing  = Lam x p
tlam x p (Just Wildcard) = Lam x p
tlam x p (Just t) = (`Anno` Pi x p t (Scope Wildcard)) . Lam x p

piType :: NameHint -> Annotation -> Maybe (Type v) -> Scope1 Expr v -> Expr v
piType x p Nothing  = Pi x p Wildcard
piType x p (Just t) = Pi x p t

anno :: Expr v -> Expr v -> Expr v
anno e Wildcard = e
anno e t        = Anno e t

apps :: Foldable t => Expr v -> t (Annotation, Expr v) -> Expr v
apps = Foldable.foldl (uncurry . App)

-------------------------------------------------------------------------------
-- * Views
globals :: Expr v -> Expr (Var Name v)
globals expr = case expr of
  Var v -> Var $ F v
  Global n -> Var $ B n
  Lit l -> Lit l
  Con c -> Con c
  Pi  h p t s -> Pi h p (globals t) (exposeScope globals s)
  Lam h p s -> Lam h p (exposeScope globals s)
  App e1 p e2 -> App (globals e1) p (globals e2)
  Case e brs -> Case (globals e) (exposeBranches globals brs)
  Anno e t -> Anno (globals e) (globals t)
  Wildcard -> Wildcard

-------------------------------------------------------------------------------
-- Instances
instance Eq1 Expr
instance Ord1 Expr
instance Show1 Expr

instance SyntaxPi Expr where
  pi_ = Pi

  piView (Pi n p e s) = Just (n, p, e, s)
  piView _ = Nothing

instance SyntaxLambda Expr where
  lam h a = tlam h a . Just

  lamView (Lam n p s) = Just (n, p, Wildcard, s)
  lamView _ = Nothing

instance SyntaxApp Expr where
  app = App

  appView (App e1 p e2) = Just (e1, p, e2)
  appView _ = Nothing

instance Syntax Expr

instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  expr >>= f = case expr of
    Var v       -> f v
    Global g    -> Global g
    Lit l       -> Lit l
    Con c       -> Con c
    Pi  n p t s -> Pi n p (t >>= f) (s >>>= f)
    Lam n p s   -> Lam n p (s >>>= f)
    App e1 p e2 -> App (e1 >>= f) p (e2 >>= f)
    Case e brs  -> Case (e >>= f) (brs >>>= f)
    Anno e t    -> Anno (e >>= f) (t >>= f)
    Wildcard    -> Wildcard

instance (Eq v, IsString v, Pretty v) => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Lit l -> prettyM l
    Con (Left c) -> prettyM c
    Con (Right qc) -> prettyM qc
    Pi  h a Wildcard s -> withNameHint h $ \x -> parens `above` absPrec $
      "forall" <+> inviolable (prettyAnnotation a $ prettyM x)
      <> "." <+> associate absPrec (prettyM $ instantiate1 (pure $ fromText x) s)
    Pi  h a t s -> withNameHint h $ \x -> parens `above` absPrec $
      "forall" <+> inviolable (prettyAnnotation a $ prettyM x)
      <+> ":" <+> inviolable (prettyM t)
      <> "." <+> associate absPrec (prettyM $ instantiate1 (pure $ fromText x) s)
    Lam h a s -> withNameHint h $ \x -> parens `above` absPrec $
      "\\" <+> inviolable (prettyAnnotation a $ prettyM x)
        <> "." <+> associate absPrec (prettyM $ instantiate1 (pure $ fromText x) s)
    App e1 a e2 -> prettyApp (prettyM e1) (prettyAnnotation a $ prettyM e2)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+> "of" <$$> indent 2 (prettyM brs)
    Anno e t  -> parens `above` annoPrec $
      prettyM e <+> ":" <+> associate casePrec (prettyM t)
    Wildcard -> "_"
