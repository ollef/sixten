{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Syntax.Pre.Pattern where

import Protolude

import Data.Bifoldable
import Data.Bitraversable
import Data.Functor.Classes
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Syntax
import Util

data Pat con lit typ b
  = VarPat b
  | WildcardPat
  | LitPat lit
  | ConPat con (Vector (Plicitness, Pat con lit typ b))
  | AnnoPat (Pat con lit typ b) typ
  | ViewPat typ (Pat con lit typ b)
  | PatLoc !SourceLoc (Pat con lit typ b)
  deriving (Foldable, Functor, Show, Traversable)

-------------------------------------------------------------------------------
-- Helpers
liftPatEq
  :: (con1 -> con2 -> Bool)
  -> (lit1 -> lit2 -> Bool)
  -> (typ1 -> typ2 -> Bool)
  -> (a -> b -> Bool)
  -> Pat con1 lit1 typ1 a
  -> Pat con2 lit2 typ2 b
  -> Bool
liftPatEq _ _ _ g (VarPat a) (VarPat b) = g a b
liftPatEq _ _ _ _ WildcardPat WildcardPat = True
liftPatEq _ l _ _ (LitPat l1) (LitPat l2) = l l1 l2
liftPatEq e l f g (ConPat c1 as1) (ConPat c2 as2)
  = e c1 c2
  && liftEq (\(p1, pat1) (p2, pat2) -> p1 == p2 && liftPatEq e l f g pat1 pat2) as1 as2
liftPatEq e l f g (AnnoPat p1 t1) (AnnoPat p2 t2) = liftPatEq e l f g p1 p2 && f t1 t2
liftPatEq e l f g (ViewPat t1 p1) (ViewPat t2 p2) = f t1 t2 && liftPatEq e l f g p1 p2
liftPatEq e l f g (PatLoc _ p1) p2 = liftPatEq e l f g p1 p2
liftPatEq e l f g p1 (PatLoc _ p2) = liftPatEq e l f g p1 p2
liftPatEq _ _ _ _ _ _ = False

patternHint :: Monoid b => Pat con lit typ b -> b
patternHint (unPatLoc -> VarPat b) = b
patternHint _ = mempty

unPatLoc :: Pat con lit typ b -> Pat con lit typ b
unPatLoc (PatLoc _ p) = unPatLoc p
unPatLoc p = p

bindPatLits
  :: (lit -> Pat con lit' typ b)
  -> Pat con lit typ b
  -> Pat con lit' typ b
bindPatLits f pat = case pat of
  VarPat v -> VarPat v
  WildcardPat -> WildcardPat
  LitPat l -> f l
  ConPat c ps -> ConPat c (second (bindPatLits f) <$> ps)
  AnnoPat p t -> AnnoPat (bindPatLits f p) t
  ViewPat e p -> ViewPat e (bindPatLits f p)
  PatLoc loc p -> PatLoc loc (bindPatLits f p)

-------------------------------------------------------------------------------
-- Instances
instance (Eq con, Eq lit, Eq typ, Eq b) => Eq (Pat con lit typ b) where
  VarPat b1 == VarPat b2 = b1 == b2
  WildcardPat == WildcardPat = True
  LitPat l1 == LitPat l2 = l1 == l2
  ConPat c1 as1 == ConPat c2 as2 = c1 == c2 && as1 == as2
  AnnoPat t1 p1 == AnnoPat t2 p2 = t1 == t2 && p1 == p2
  ViewPat t1 p1 == ViewPat t2 p2 = t1 == t2 && p1 == p2
  PatLoc _ pat1 == pat2 = pat1 == pat2
  pat1 == PatLoc _ pat2 = pat1 == pat2
  _ == _ = False

instance Applicative (Pat con lit typ) where
  pure = return
  (<*>) = ap

instance Monad (Pat con lit typ) where
  return = VarPat
  pat >>= f = case pat of
    VarPat b -> f b
    WildcardPat -> WildcardPat
    LitPat l -> LitPat l
    ConPat c pats -> ConPat c [(a, p >>= f) | (a, p) <- pats]
    AnnoPat p t -> AnnoPat (p >>= f) t
    ViewPat t p -> ViewPat t $ p >>= f
    PatLoc loc p -> PatLoc loc $ p >>= f

instance Bifunctor (Pat con lit) where bimap = bimapDefault
instance Bifoldable (Pat con lit) where bifoldMap = bifoldMapDefault

instance Bitraversable (Pat con lit) where
  bitraverse f g pat = case pat of
    VarPat b -> VarPat <$> g b
    WildcardPat -> pure WildcardPat
    LitPat l -> pure $ LitPat l
    ConPat c pats -> ConPat c <$> traverse (traverse (bitraverse f g)) pats
    AnnoPat p t -> AnnoPat <$> bitraverse f g p <*> f t
    ViewPat t p -> ViewPat <$> f t <*> bitraverse f g p
    PatLoc loc p -> PatLoc loc <$> bitraverse f g p

prettyPattern
  :: (Pretty con, Pretty lit, Pretty typ)
  => Vector Name
  -> Pat con lit typ b
  -> PrettyDoc
prettyPattern names = prettyM . fmap ((names Vector.!) . fst) . indexed

instance (Pretty con, Pretty lit, Pretty typ, Pretty b) => Pretty (Pat con lit typ b) where
  prettyM pat = case pat of
    VarPat b -> prettyM b
    WildcardPat -> "_"
    LitPat l -> prettyM l
    ConPat c args -> prettyApps (prettyM c) $ (\(p, arg) -> prettyAnnotation p $ prettyM arg) <$> args
    AnnoPat p t -> parens `above` annoPrec $
      prettyM p <+> ":" <+> prettyM t
    ViewPat t p -> parens `above` arrPrec $
      prettyM t <+> "->" <+> prettyM p
    PatLoc _ p -> prettyM p
