{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, MonadComprehensions, OverloadedStrings #-}
module Syntax.Concrete.Pattern where

import Control.Monad
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Functor.Classes
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Syntax
import Util

data Pat con typ b
  = VarPat !NameHint b
  | WildcardPat
  | LitPat Literal
  | ConPat con (Vector (Plicitness, Pat con typ b))
  | AnnoPat (Pat con typ b) typ
  | ViewPat typ (Pat con typ b)
  | PatLoc !SourceLoc (Pat con typ b)
  deriving (Foldable, Functor, Show, Traversable)

-------------------------------------------------------------------------------
-- Helpers
liftPatEq
  :: (con1 -> con2 -> Bool)
  -> (typ1 -> typ2 -> Bool)
  -> (a -> b -> Bool)
  -> Pat con1 typ1 a
  -> Pat con2 typ2 b
  -> Bool
liftPatEq _ _ g (VarPat _ a) (VarPat _ b) = g a b
liftPatEq _ _ _ WildcardPat WildcardPat = True
liftPatEq _ _ _ (LitPat l1) (LitPat l2) = l1 == l2
liftPatEq e f g (ConPat c1 as1) (ConPat c2 as2)
  = e c1 c2
  && liftEq (\(p1, pat1) (p2, pat2) -> p1 == p2 && liftPatEq e f g pat1 pat2) as1 as2
liftPatEq e f g (AnnoPat p1 t1) (AnnoPat p2 t2) = liftPatEq e f g p1 p2 && f t1 t2
liftPatEq e f g (ViewPat t1 p1) (ViewPat t2 p2) = f t1 t2 && liftPatEq e f g p1 p2
liftPatEq e f g (PatLoc _ p1) p2 = liftPatEq e f g p1 p2
liftPatEq e f g p1 (PatLoc _ p2) = liftPatEq e f g p1 p2
liftPatEq _ _ _ _ _ = False

nameHints :: Pat con typ b -> Vector NameHint
nameHints pat = case pat of
  VarPat h _ -> pure h
  WildcardPat -> mempty
  LitPat _ -> mempty
  ConPat _ ps -> ps >>= nameHints . snd
  AnnoPat p _ -> nameHints p
  ViewPat _ p -> nameHints p
  PatLoc _ p -> nameHints p

patternHint :: Pat con typ b -> NameHint
patternHint (VarPat h _) = h
patternHint (PatLoc _ p) = patternHint p
patternHint _ = mempty

varPatView
  :: Pat con t ()
  -> Maybe NameHint
varPatView (PatLoc _ p) = varPatView p
varPatView (VarPat h ~()) = Just h
varPatView WildcardPat = Just mempty
varPatView _ = Nothing

-------------------------------------------------------------------------------
-- Instances
instance (Eq con, Eq typ, Eq b) => Eq (Pat con typ b) where
  VarPat h1 b1 == VarPat h2 b2 = h1 == h2 && b1 == b2
  WildcardPat == WildcardPat = True
  LitPat l1 == LitPat l2 = l1 == l2
  ConPat c1 as1 == ConPat c2 as2 = c1 == c2 && as1 == as2
  AnnoPat t1 p1 == AnnoPat t2 p2 = t1 == t2 && p1 == p2
  ViewPat t1 p1 == ViewPat t2 p2 = t1 == t2 && p1 == p2
  PatLoc _ pat1 == pat2 = pat1 == pat2
  pat1 == PatLoc _ pat2 = pat1 == pat2
  _ == _ = False

instance Applicative (Pat con typ) where
  pure = return
  (<*>) = ap

instance Monad (Pat con typ) where
  return = VarPat mempty
  pat >>= f = case pat of
    VarPat h b -> case f b of
      VarPat h' b' -> VarPat (h' <> h) b'
      fb -> fb
    WildcardPat -> WildcardPat
    LitPat l -> LitPat l
    ConPat c pats -> ConPat c [(a, p >>= f) | (a, p) <- pats]
    AnnoPat p t -> AnnoPat (p >>= f) t
    ViewPat t p -> ViewPat t $ p >>= f
    PatLoc loc p -> PatLoc loc $ p >>= f

instance Bifunctor (Pat con) where bimap = bimapDefault
instance Bifoldable (Pat con) where bifoldMap = bifoldMapDefault

instance Bitraversable (Pat con) where
  bitraverse f g pat = case pat of
    VarPat h b -> VarPat h <$> g b
    WildcardPat -> pure WildcardPat
    LitPat l -> pure $ LitPat l
    ConPat c pats -> ConPat c <$> traverse (traverse (bitraverse f g)) pats
    AnnoPat p t -> AnnoPat <$> bitraverse f g p <*> f t
    ViewPat t p -> ViewPat <$> f t <*> bitraverse f g p
    PatLoc loc p -> PatLoc loc <$> bitraverse f g p

prettyPattern
  :: (Pretty con, Pretty typ)
  => Vector Name
  -> Pat con typ b
  -> PrettyM Doc
prettyPattern names = prettyM . fmap ((names Vector.!) . fst) . indexed

instance (Pretty con, Pretty typ, Pretty b) => Pretty (Pat con typ b) where
  prettyM pat = case pat of
    VarPat _ b -> prettyM b
    WildcardPat -> "_"
    LitPat l -> prettyM l
    ConPat c args -> prettyApps (prettyM c) $ (\(p, arg) -> prettyAnnotation p $ prettyM arg) <$> args
    AnnoPat t p -> parens `above` annoPrec $
      prettyM p <+> ":" <+> prettyM t
    ViewPat t p -> parens `above` arrPrec $
      prettyM t <+> "->" <+> prettyM p
    PatLoc _ p -> prettyM p
