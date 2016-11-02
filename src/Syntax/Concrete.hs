{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, OverloadedStrings, TypeFamilies, ViewPatterns #-}
module Syntax.Concrete where

import Control.Monad
import qualified Data.Foldable as Foldable
import Data.Monoid
import Data.String
import Prelude.Extras
import Data.HashSet(HashSet)
import qualified Data.HashSet as HS

import Syntax
import Util

data Expr v
  = Var v
  | Global Name  -- ^ Really just a variable, but it's often annoying to not have it
  | Lit Literal
  | Con (Either Constr QConstr)
  | Pi !NameHint !Plicitness (Type v) (Scope1 Expr v)  -- ^ Dependent function space
  | Lam !NameHint !Plicitness (Type v) (Scope1 Expr v)
  | App (Expr v) !Plicitness (Expr v)
  | Case (Expr v) (Branches (Either Constr QConstr) Plicitness Expr v)
  | Wildcard  -- ^ Attempt to infer it
  | SourceLoc !Rendering (Expr v)
  deriving (Foldable, Functor, Show, Traversable)

-- | Synonym for documentation purposes
type Type = Expr

constructors :: Expr v -> HashSet (Either Constr QConstr)
constructors expr = case expr of
  Var _ -> mempty
  Global _ -> mempty
  Lit _ -> mempty
  Con c -> HS.singleton c
  Pi _ _ t s -> constructors t <> scopeConstrs s
  Lam _ _ t s -> constructors t <> scopeConstrs s
  App e1 _ e2 -> constructors e1 <> constructors e2
  Case e brs -> constructors e <> case brs of
    ConBranches cbrs def -> Foldable.fold
      [HS.singleton c <> teleConstrs tele <> scopeConstrs s | (c, tele, s) <- cbrs]
      <> constructors def
    LitBranches lbrs def -> Foldable.fold
      [constructors s | (_, s) <- lbrs]
      <> constructors def
  Wildcard -> mempty
  SourceLoc _ e -> constructors e
  where
    teleConstrs = Foldable.fold . fmap scopeConstrs . teleTypes
    scopeConstrs :: Scope b Expr v -> HashSet (Either Constr QConstr)
    scopeConstrs = constructors . fromScope

-- * Smart constructors
tlam :: NameHint -> Plicitness -> Maybe (Type v) -> Scope1 Expr v -> Expr v
tlam x p Nothing  = Lam x p Wildcard
tlam x p (Just t) = Lam x p t

piType :: NameHint -> Plicitness -> Maybe (Type v) -> Scope1 Expr v -> Expr v
piType x p Nothing  = Pi x p Wildcard
piType x p (Just t) = Pi x p t

-------------------------------------------------------------------------------
-- Instances
instance Eq1 Expr
instance Show1 Expr

instance Eq v => Eq (Expr v) where
  Var v1 == Var v2 = v1 == v2
  Global g1 == Global g2 = g1 == g2
  Lit l1 == Lit l2 = l1 == l2
  Con c1 == Con c2 = c1 == c2
  Pi h1 p1 t1 s1 == Pi h2 p2 t2 s2 = and [h1 == h2, p1 == p2, t1 == t2, s1 == s2]
  Lam h1 p1 t1 s1 == Lam h2 p2 t2 s2 = and [h1 == h2, p1 == p2, t1 == t2, s1 == s2]
  App e1 p1 e1' == App e2 p2 e2' = e1 == e2 && p1 == p2 && e1' == e2'
  Case e1 brs1 == Case e2 brs2 = e1 == e2 && brs1 == brs2
  Wildcard == Wildcard = True
  SourceLoc _ e1 == e2 = e1 == e2
  e1 == SourceLoc _ e2 = e1 == e2
  _ == _ = False

instance Syntax Expr where
  type Annotation Expr = Plicitness

  lam = Lam

  lamView (SourceLoc _ e) = lamView e
  lamView (Lam n p t s) = Just (n, p, t, s)
  lamView _ = Nothing

  pi_ = Pi

  piView (SourceLoc _ e) = piView e
  piView (Pi n p e s) = Just (n, p, e, s)
  piView _ = Nothing

  app = App

  appView (SourceLoc _ e) = appView e
  appView (App e1 p e2) = Just (e1, p, e2)
  appView _ = Nothing

instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  expr >>= f = case expr of
    Var v -> f v
    Global g -> Global g
    Lit l -> Lit l
    Con c -> Con c
    Pi  n p t s -> Pi n p (t >>= f) (s >>>= f)
    Lam n p t s -> Lam n p (t >>= f) (s >>>= f)
    App e1 p e2 -> App (e1 >>= f) p (e2 >>= f)
    Case e brs -> Case (e >>= f) (brs >>>= f)
    SourceLoc r e -> SourceLoc r (e >>= f)
    Wildcard -> Wildcard

instance (Eq v, IsString v, Pretty v) => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Lit l -> prettyM l
    Con (Left c) -> prettyM c
    Con (Right qc) -> prettyM qc
    Pi _ p t (unusedScope -> Just e) -> parens `above` arrPrec $
      prettyAnnotation p (prettyM t)
      <+> "->" <+>
      associate arrPrec (prettyM e)
    (usedPisViewM -> Just (tele, s)) -> withTeleHints tele $ \ns ->
      parens `above` absPrec $
      prettyTeleVarTypes ns tele <+> "->" <+>
      associate arrPrec (prettyM $ instantiateTele (pure . fromText <$> ns) s)
    Pi {} -> error "impossible prettyPrec pi"
    (lamsViewM -> Just (tele, s)) -> withTeleHints tele $ \ns ->
      parens `above` absPrec $
      "\\" <> prettyTeleVarTypes ns tele <> "." <+>
      prettyM (instantiateTele (pure . fromText <$> ns) s)
    Lam {} -> error "impossible prettyPrec lam"
    App e1 p e2 -> prettyApp (prettyM e1) (prettyAnnotation p $ prettyM e2)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+> "of" <$$> indent 2 (prettyM brs)
    Wildcard -> "_"
    SourceLoc _ e -> prettyM e
