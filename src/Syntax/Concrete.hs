{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, OverloadedStrings, ViewPatterns #-}
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
  | Pi !NameHint !Annotation (Type v) (Scope1 Expr v)  -- ^ Dependent function space
  | Lam !NameHint !Annotation (Type v) (Scope1 Expr v)
  | App (Expr v) !Annotation (Expr v)
  | Case (Expr v) (Branches (Either Constr QConstr) Expr v)
  | Anno (Expr v) (Expr v)
  | Wildcard  -- ^ Attempt to infer it
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-- | Synonym for documentation purposes
type Type = Expr

constructors :: Expr v -> HashSet (Either Constr QConstr)
constructors expr = case expr of
  Var _ -> mempty
  Global _ -> mempty
  Lit _ -> mempty
  Con c -> HS.singleton c
  Pi  _ _ t s -> constructors t <> scopeConstrs s
  Lam _ _ t s -> constructors t <> scopeConstrs s
  App e1 _ e2 -> constructors e1 <> constructors e2
  Case e brs -> constructors e <> case brs of
    ConBranches cbrs def -> Foldable.fold
      [HS.singleton c <> teleConstrs tele <> scopeConstrs s | (c, tele, s) <- cbrs]
      <> constructors def
    LitBranches lbrs def -> Foldable.fold
      [constructors s | (_, s) <- lbrs]
      <> constructors def
  Anno e t -> constructors e <> constructors t
  Wildcard -> mempty
  where
    teleConstrs = Foldable.fold . fmap scopeConstrs . teleTypes
    scopeConstrs = constructors . fromScope

-- * Smart constructors
tlam :: NameHint -> Annotation -> Maybe (Type v) -> Scope1 Expr v -> Expr v
tlam x p Nothing  = Lam x p Wildcard
tlam x p (Just t) = Lam x p t

piType :: NameHint -> Annotation -> Maybe (Type v) -> Scope1 Expr v -> Expr v
piType x p Nothing  = Pi x p Wildcard
piType x p (Just t) = Pi x p t

anno :: Expr v -> Type v -> Expr v
anno e Wildcard = e
anno (Lam h1 a1 Wildcard s1) (Pi h2 a2 t2 s2)
  | a1 == a2
    = Lam (h1 <> h2) a1 t2
    $ annoScope s1 s2
anno e@(Lam _ a1 _ _) t@(Pi h2 a2 _ _)
  | plicitness a1 == Explicit
  && plicitness a2 == Implicit
  = anno (Lam h2 a2 Wildcard $ abstractNone e) t
anno e t = Anno e t

annoScope :: Scope b Expr v -> Scope b Type v -> Scope b Expr v
annoScope e t = toScope $ anno (fromScope e) (fromScope t)

apps :: Foldable t => Expr v -> t (Annotation, Expr v) -> Expr v
apps = Foldable.foldl (uncurry . App)

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
  lam = Lam

  lamView (Lam n p t s) = Just (n, p, t, s)
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
    Lam n p t s -> Lam n p (t >>= f) (s >>>= f)
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
    Pi  _ a t (unusedScope -> Just e) -> parens `above` arrPrec $
      prettyAnnotation a (prettyM t)
      <+> "->" <+>
      associate arrPrec (prettyM e)
    (usedPisViewM -> Just (tele, s)) -> withTeleHints tele $ \ns ->
      parens `above` absPrec $
      "forall" <+> prettyTeleVarTypes ns tele <> "." <+>
      prettyM (instantiateTele (pure . fromText <$> ns) s)
    Pi {} -> error "impossible prettyPrec pi"
    (lamsViewM -> Just (tele, s)) -> withTeleHints tele $ \ns ->
      parens `above` absPrec $
      "\\" <> prettyTeleVarTypes ns tele <> "." <+>
      prettyM (instantiateTele (pure . fromText <$> ns) s)
    Lam {} -> error "impossible prettyPrec lam"
    App e1 a e2 -> prettyApp (prettyM e1) (prettyAnnotation a $ prettyM e2)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+> "of" <$$> indent 2 (prettyM brs)
    Anno e t  -> parens `above` annoPrec $
      prettyM e <+> ":" <+> associate casePrec (prettyM t)
    Wildcard -> "_"
