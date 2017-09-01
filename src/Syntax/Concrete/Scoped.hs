{-# LANGUAGE OverloadedStrings #-}
module Syntax.Concrete.Scoped
  ( module Definition
  , module Pattern
  , Expr(..), Type
  , piView --, pisView
  ) where

import Control.Monad
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import Data.Functor.Classes
import Data.HashSet(HashSet)
import Data.Monoid
import Data.String
import Data.Traversable

import Syntax hiding (piView)
import Syntax.Concrete.Definition as Definition
import Syntax.Concrete.Pattern as Pattern
import Util

data Expr v
  = Var v
  | Global QName
  | Lit Literal
  | Con (HashSet QConstr)
  | Pi !Plicitness (Pat (PatternScope Type v) ()) (PatternScope Expr v)
  | Lam !Plicitness (Pat (PatternScope Type v) ()) (PatternScope Expr v)
  | App (Expr v) !Plicitness (Expr v)
  | Let !NameHint (Expr v) (Scope1 Expr v)
  | Case (Expr v) [(Pat (PatternScope Type v) (), PatternScope Expr v)]
  | ExternCode (Extern (Expr v))
  | Wildcard
  | SourceLoc !SourceLoc (Expr v)

-- | Synonym for documentation purposes
type Type = Expr

piView :: Expr v -> Maybe (Plicitness, Pat (PatternScope Type v) (), PatternScope Expr v)
piView (Pi p pat s) = Just (p, pat, s)
piView _ = Nothing

-- pisView :: Expr v -> (PatternTelescope Con Expr v, Scope PatternVar Expr v)
-- pisView = patBindingsView Syntax.Concrete.piView

-------------------------------------------------------------------------------
-- Instances
-- deriveShow1 ''Expr
-- deriveShow ''Expr

instance Eq1 Expr where
  liftEq f (Var v1) (Var v2) = f v1 v2
  liftEq _ (Global g1) (Global g2) = g1 == g2
  liftEq _ (Lit l1) (Lit l2) = l1 == l2
  liftEq _ (Con c1) (Con c2) = c1 == c2
  liftEq f (Pi p1 pat1 s1) (Pi p2 pat2 s2) = and [p1 == p2, liftPatEq (liftEq f) (==) pat1 pat2, liftEq f s1 s2]
  liftEq f (Lam p1 pat1 s1) (Lam p2 pat2 s2) = and [p1 == p2, liftPatEq (liftEq f) (==) pat1 pat2, liftEq f s1 s2]
  liftEq f (App e1 p1 e1') (App e2 p2 e2') = liftEq f e1 e2 && p1 == p2 && liftEq f e1' e2'
  liftEq f (Let h1 e1 s1) (Let h2 e2 s2) = h1 == h2 && liftEq f e1 e2 && liftEq f s1 s2
  liftEq f (Case e1 brs1) (Case e2 brs2)
    = liftEq f e1 e2
    && liftEq (\(pat1, s1) (pat2, s2) -> liftPatEq (liftEq f) (==) pat1 pat2 && liftEq f s1 s2) brs1 brs2
  liftEq f (ExternCode c) (ExternCode c') = liftEq (liftEq f) c c'
  liftEq _ Wildcard Wildcard = True
  liftEq f (SourceLoc _ e1) e2 = liftEq f e1 e2
  liftEq f e1 (SourceLoc _ e2) = liftEq f e1 e2
  liftEq _ _ _ = False

instance Eq v => Eq (Expr v) where
  (==) = liftEq (==)

instance AppSyntax Expr where
  app = App

  appView (App e1 p e2) = Just (e1, p, e2)
  appView _ = Nothing

instance GlobalBind Expr where
  global = Global
  bind f g expr = case expr of
    Var v -> f v
    Global v -> g v
    Lit l -> Lit l
    Con c -> Con c
    Pi p pat s -> Pi p (first (bound f g) pat) (bound f g s)
    Lam p pat s -> Lam p (first (bound f g) pat) (bound f g s)
    App e1 p e2 -> App (bind f g e1) p (bind f g e2)
    Let h e s -> Let h (bind f g e) (bound f g s)
    Case e brs -> Case (bind f g e) (bimap (first (bound f g)) (bound f g) <$> brs)
    ExternCode c -> ExternCode (bind f g <$> c)
    Wildcard -> Wildcard
    SourceLoc r e -> SourceLoc r (bind f g e)

instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  expr >>= f = bind f Global expr

instance Functor Expr where fmap = fmapDefault
instance Foldable Expr where foldMap = foldMapDefault

instance Traversable Expr where
  traverse f expr = case expr of
    Var v -> Var <$> f v
    Global v -> pure $ Global v
    Lit l -> pure $ Lit l
    Con c -> pure $ Con c
    Pi p pat s -> Pi p <$> bitraverse (traverse f) pure pat <*> traverse f s
    Lam p pat s -> Lam p <$> bitraverse (traverse f) pure pat <*> traverse f s
    App e1 p e2 -> App <$> traverse f e1 <*> pure p <*> traverse f e2
    Let h e s -> Let h <$> traverse f e <*> traverse f s
    Case e brs -> Case
      <$> traverse f e
      <*> traverse (bitraverse (bitraverse (traverse f) pure) (traverse f)) brs
    ExternCode c -> ExternCode <$> traverse (traverse f) c
    SourceLoc r e -> SourceLoc r <$> traverse f e
    Wildcard -> pure Wildcard

instance (Eq v, IsString v, Pretty v) => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Lit l -> prettyM l
    Con c -> prettyM $ toList c
    Pi p pat s -> withNameHints (nameHints pat) $ \ns -> do
      let inst = instantiatePattern (pure . fromName) ns
      parens `above` absPrec $
        prettyAnnotation p (prettyPattern ns $ first inst pat) <+> "->" <+>
          associate absPrec (prettyM $ inst s)
    Lam p pat s -> withNameHints (nameHints pat) $ \ns -> do
      let inst = instantiatePattern (pure . fromName) ns
      parens `above` absPrec $
        "\\" <> prettyAnnotation p (prettyPattern ns $ first inst pat) <> "." <+>
          associate absPrec (prettyM $ inst s)
    App e1 p e2 -> prettyApp (prettyM e1) (prettyAnnotation p $ prettyM e2)
    Let h e s -> parens `above` letPrec $ withNameHint h $ \n ->
      "let" <+> prettyM n <+> "=" <+> inviolable (prettyM e) <+>
      "in" <+> prettyM (Util.instantiate1 (pure $ fromName n) s)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+> "of" <$$> indent 2 (vcat $ prettyBranch <$> brs)
    ExternCode c -> prettyM c
    Wildcard -> "_"
    SourceLoc _ e -> prettyM e
    where
      prettyBranch (pat, br) = withNameHints (nameHints pat) $ \ns -> do
        let inst = instantiatePattern (pure . fromName) ns
        prettyPattern ns (first inst pat) <+> "->" <+> prettyM (inst br)
