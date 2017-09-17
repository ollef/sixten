{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, MonadComprehensions, OverloadedStrings #-}
module Syntax.Concrete.Pattern where

import Control.Monad
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import Data.Functor.Classes
import Data.HashSet(HashSet)
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Syntax
import Util

data Pat typ b
  = VarPat !NameHint b
  | WildcardPat
  | LitPat Literal
  | ConPat (HashSet QConstr) (Vector (Plicitness, Pat typ b))
  | AnnoPat typ (Pat typ b)
  | ViewPat typ (Pat typ b)
  | PatLoc !SourceLoc (Pat typ b)
  deriving (Foldable, Functor, Show, Traversable)

-------------------------------------------------------------------------------
-- Helpers
patEq :: (typ1 -> typ2 -> Bool) -> (a -> b -> Bool) -> Pat typ1 a -> Pat typ2 b -> Bool
patEq _ g (VarPat _ a) (VarPat _ b) = g a b
patEq _ _ WildcardPat WildcardPat = True
patEq _ _ (LitPat l1) (LitPat l2) = l1 == l2
patEq f g (ConPat qc1 as1) (ConPat qc2 as2)
  = qc1 == qc2
  && liftEq (\(p1, pat1) (p2, pat2) -> p1 == p2 && patEq f g pat1 pat2) as1 as2
patEq f g (AnnoPat t1 p1) (AnnoPat t2 p2) = f t1 t2 && patEq f g p1 p2
patEq f g (ViewPat t1 p1) (ViewPat t2 p2) = f t1 t2 && patEq f g p1 p2
patEq f g (PatLoc _ p1) p2 = patEq f g p1 p2
patEq f g p1 (PatLoc _ p2) = patEq f g p1 p2
patEq _ _ _ _ = False

nameHints :: Pat typ b -> Vector NameHint
nameHints pat = case pat of
  VarPat h _ -> pure h
  WildcardPat -> mempty
  LitPat _ -> mempty
  ConPat _ ps -> ps >>= nameHints . snd
  AnnoPat _ p -> nameHints p
  ViewPat _ p -> nameHints p
  PatLoc _ p -> nameHints p

patternHint :: Pat typ b -> NameHint
patternHint (VarPat h _) = h
patternHint (PatLoc _ p) = patternHint p
patternHint _ = mempty

liftPatEq
  :: (typ1 -> typ2 -> Bool)
  -> (a -> b -> Bool)
  -> Pat typ1 a
  -> Pat typ2 b
  -> Bool
liftPatEq _ g (VarPat _ a) (VarPat _ b) = g a b
liftPatEq _ _ WildcardPat WildcardPat = True
liftPatEq _ _ (LitPat l1) (LitPat l2) = l1 == l2
liftPatEq f g (ConPat c1 ps1) (ConPat c2 ps2)
  = c1 == c2
  && liftEq (\(p1, pat1) (p2, pat2) -> p1 == p2 && liftPatEq f g pat1 pat2) ps1 ps2
liftPatEq f g (AnnoPat typ1 pat1) (AnnoPat typ2 pat2) = f typ1 typ2 && liftPatEq f g pat1 pat2
liftPatEq f g (ViewPat typ1 pat1) (ViewPat typ2 pat2) = f typ1 typ2 && liftPatEq f g pat1 pat2
liftPatEq f g (PatLoc _ pat1) pat2 = liftPatEq f g pat1 pat2
liftPatEq f g pat1 (PatLoc _ pat2) = liftPatEq f g pat1 pat2
liftPatEq _ _ _ _ = False

-------------------------------------------------------------------------------
-- Instances
instance (Eq typ, Eq b) => Eq (Pat typ b) where
  VarPat h1 b1 == VarPat h2 b2 = h1 == h2 && b1 == b2
  WildcardPat == WildcardPat = True
  LitPat l1 == LitPat l2 = l1 == l2
  ConPat c1 as1 == ConPat c2 as2 = c1 == c2 && as1 == as2
  AnnoPat t1 p1 == AnnoPat t2 p2 = t1 == t2 && p1 == p2
  ViewPat t1 p1 == ViewPat t2 p2 = t1 == t2 && p1 == p2
  PatLoc _ pat1 == pat2 = pat1 == pat2
  pat1 == PatLoc _ pat2 = pat1 == pat2
  _ == _ = False

instance Applicative (Pat typ) where
  pure = return
  (<*>) = ap

instance Monad (Pat typ) where
  return = VarPat mempty
  pat >>= f = case pat of
    VarPat h b -> case f b of
      VarPat h' b' -> VarPat (h' <> h) b'
      fb -> fb
    WildcardPat -> WildcardPat
    LitPat l -> LitPat l
    ConPat c pats -> ConPat c [(a, p >>= f) | (a, p) <- pats]
    AnnoPat t p -> AnnoPat t $ p >>= f
    ViewPat t p -> ViewPat t $ p >>= f
    PatLoc loc p -> PatLoc loc $ p >>= f

instance Bifunctor Pat where bimap = bimapDefault
instance Bifoldable Pat where bifoldMap = bifoldMapDefault

instance Bitraversable Pat where
  bitraverse f g pat = case pat of
    VarPat h b -> VarPat h <$> g b
    WildcardPat -> pure WildcardPat
    LitPat l -> pure $ LitPat l
    ConPat c pats -> ConPat c <$> traverse (traverse (bitraverse f g)) pats
    AnnoPat t p -> AnnoPat <$> f t <*> bitraverse f g p
    ViewPat t p -> ViewPat <$> f t <*> bitraverse f g p
    PatLoc loc p -> PatLoc loc <$> bitraverse f g p

prettyPattern
  :: Pretty typ
  => Vector Name
  -> Pat typ b
  -> PrettyM Doc
prettyPattern names = prettyM . fmap ((names Vector.!) . fst) . indexed

instance (Pretty typ, Pretty b) => Pretty (Pat typ b) where
  prettyM pat = case pat of
    VarPat _ b -> prettyM b
    WildcardPat -> "_"
    LitPat l -> prettyM l
    ConPat c args -> prettyApps (prettyM $ toList c) $ (\(p, arg) -> prettyAnnotation p $ prettyM arg) <$> args
    AnnoPat t p -> parens `above` annoPrec $
      prettyM p <+> ":" <+> prettyM t
    ViewPat t p -> parens `above` arrPrec $
      prettyM t <+> "->" <+> prettyM p
    PatLoc _ p -> prettyM p
