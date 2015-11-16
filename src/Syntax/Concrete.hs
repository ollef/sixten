{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts #-}
module Syntax.Concrete where

import Control.Monad
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
  | Type  -- ^ Type : Type
  | Pi  !NameHint !Plicitness (Type v) (Scope1 Expr v)  -- ^ Dependent function space
  | Lam !NameHint !Plicitness (Scope1 Expr v)
  | App (Expr v) !Plicitness (Expr v)
  | Case (Expr v) (Branches Expr v)
  | Anno (Expr v) (Expr v)
  | Wildcard  -- ^ Attempt to infer it
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-- | Synonym for documentation purposes
type Type = Expr

-- * Smart constructors
lam :: NameHint -> Plicitness -> Maybe (Type v) -> Scope1 Expr v -> Expr v
lam x p Nothing  = Lam x p
lam x p (Just t) = (`Anno` Pi x p t (Scope Wildcard)) . Lam x p

piType :: NameHint -> Plicitness -> Maybe (Type v) -> Scope1 Expr v -> Expr v
piType x p Nothing  = Pi x p Wildcard
piType x p (Just t) = Pi x p t

anno :: Expr v -> Expr v -> Expr v
anno e Wildcard = e
anno e t        = Anno e t

apps :: Expr v -> [(Plicitness, Expr v)] -> Expr v
apps = foldl (uncurry . App)

-------------------------------------------------------------------------------
-- * Views
piView :: Expr v -> Maybe (NameHint, Plicitness, Type v, Scope1 Expr v)
piView (Pi n p e s) = Just (n, p, e, s)
piView _            = Nothing

globals :: Expr v -> Expr (Var Name v)
globals expr = case expr of
  Var v -> Var $ F v
  Global n -> Var $ B n
  Lit l -> Lit l
  Con c -> Con c
  Type -> Type
  Pi  h p t s -> Pi h p (globals t) (exposeScope globals s)
  Lam h p s -> Lam h p (exposeScope globals s)
  App e1 p e2 -> App (globals e1) p (globals e2)
  Case e brs -> Case (globals e) (exposeBranches globals brs)
  Anno e t -> Anno (globals e) (globals t)
  Wildcard -> Wildcard

-------------------------------------------------------------------------------
-- Instances
instance Eq1 Expr; instance Ord1 Expr; instance Show1 Expr

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
    Type        -> Type
    Pi  n p t s -> Pi n p (t >>= f) (s >>>= f)
    Lam n p s   -> Lam n p (s >>>= f)
    App e1 p e2 -> App (e1 >>= f) p (e2 >>= f)
    Case e brs  -> Case (e >>= f) (brs >>>= f)
    Anno e t    -> Anno (e >>= f) (t >>= f)
    Wildcard    -> Wildcard

instance (IsString v, Pretty v) => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v     -> prettyM v
    Global g  -> prettyM g
    Lit l     -> prettyM l
    Con c     -> prettyM c
    Type      -> pure $ text "Type"
    Pi  h p Wildcard s -> withNameHint h $ \x -> parens `above` absPrec $
      prettyM "forall" <+> inviolable (braces `iff` (p == Implicit) $ prettyM x)
      <> prettyM "." <+> associate  (prettyM $ instantiate1 (pure $ fromText x) s)
    Pi  h p t s -> withNameHint h $ \x -> parens `above` absPrec $
      prettyM "forall" <+> inviolable (braces `iff` (p == Implicit) $ prettyM x)
      <+> prettyM ":" <+> inviolable (prettyM t)
      <> prettyM "." <+> associate  (prettyM $ instantiate1 (pure $ fromText x) s)
    Lam h p s -> withNameHint h $ \x -> parens `above` absPrec $
      prettyM "\\" <+> inviolable (braces `iff` (p == Implicit) $ prettyM x)
        <> prettyM "." <+> associate  (prettyM $ instantiate1 (pure $ fromText x) s)
    App e1 p e2 -> prettyApp (prettyM e1) (braces `iff` (p == Implicit) $ prettyM e2)
    Case e brs -> parens `above` casePrec $
      prettyM "case" <+> inviolable (prettyM e) <+> prettyM "of" <$$> prettyM brs
    Anno e t  -> parens `above` annoPrec $
      prettyM e <+> prettyM ":" <+> associate (prettyM t)
    Wildcard  -> pure $ text "_"
