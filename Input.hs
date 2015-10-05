{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Input where

import Bound
import Control.Monad
import Data.Map(Map)
import Data.Monoid
import Data.String
import Prelude.Extras

import Annotation
import Branches
import Hint
import Util
import Pretty

data Expr v
  = Var v
  | Type                                      -- ^ Type : Type
  | Pi  !NameHint !Plicitness (Maybe (Type v)) (Scope1 Expr v) -- ^ Dependent function space
  | Lam !NameHint !Plicitness (Scope1 Expr v)
  | App (Expr v) !Plicitness (Expr v)
  | Case (Expr v) (Branches Expr v)
  | Anno (Expr v) (Expr v)
  | Wildcard                         -- ^ Attempt to infer it
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-- | Synonym for documentation purposes
type Type = Expr

-- * Smart constructors
lam :: NameHint -> Plicitness -> Maybe (Type v) -> Scope1 Expr v -> Expr v
lam x p Nothing  = Lam x p
lam x p (Just t) = (`Anno` Pi x p (Just t) (Scope Wildcard)) . Lam x p

anno :: Expr v -> Expr v -> Expr v
anno e Wildcard = e
anno e t        = Anno e t

-- | A definition or type declaration on the top-level
data TopLevel v
  = DefLine  (Maybe v) (Expr v) -- ^ Maybe v means that we can use wildcard names that refer e.g. to the previous top-level thing
  | TypeDecl v         (Type v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

type Program v = Map v (Expr v, Type v)

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
    Type        -> Type
    Pi  n p t s -> Pi n p ((>>= f) <$> t) (s >>>= f)
    Lam n p s   -> Lam n p (s >>>= f)
    App e1 p e2 -> App (e1 >>= f) p (e2 >>= f)
    Case e brs  -> Case (e >>= f) (brs >>>= f)
    Anno e t    -> Anno (e >>= f) (t >>= f)
    Wildcard    -> Wildcard

instance (IsString v, Pretty v) => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v     -> prettyM v
    Type      -> pure $ text "Type"
    Pi  h p Nothing s -> withNameHint h $ \x -> parens `above` absPrec $
      prettyM "forall" <+> inviolable (braces `iff` (p == Implicit) $ prettyM x)
      <> prettyM "." <+> associate  (prettyM $ instantiate1 (pure $ fromText x) s)
    Pi  h p (Just t) s -> withNameHint h $ \x -> parens `above` absPrec $
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
