{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module Syntax.Pattern where

import Protolude

import Bound
import Data.Bifoldable
import Data.Bitraversable
import Data.Deriving
import Data.Hashable.Lifted
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Error
import Pretty
import Syntax.Annotation
import Syntax.Name
import Util

data Pat con lit b typ
  = VarPat b
  | WildcardPat
  | LitPat lit
  | ConPat con (Vector (Plicitness, Pat con lit b typ))
  | AnnoPat (Pat con lit b typ) typ
  | ViewPat typ (Pat con lit b typ)
  | ForcedPat typ
  | PatLoc !SourceLoc (Pat con lit b typ)
  deriving (Eq, Foldable, Functor, Show, Traversable, Generic, Hashable, Generic1, Hashable1)

type PatternScope = Scope PatternVar

newtype PatternVar = PatternVar Int
  deriving (Eq, Ord, Show, Generic)
  deriving newtype (Num, Hashable)

unPatternVar :: PatternVar -> Int
unPatternVar (PatternVar i) = i

-------------------------------------------------------------------------------
-- Helpers
patternHint :: Monoid b => Pat con lit b typ -> b
patternHint (unPatLoc -> VarPat b) = b
patternHint _ = mempty

unPatLoc :: Pat con lit typ b -> Pat con lit typ b
unPatLoc (PatLoc _ p) = unPatLoc p
unPatLoc p = p

bindPatLits
  :: (lit -> Pat con lit' b typ)
  -> Pat con lit b typ
  -> Pat con lit' b typ
bindPatLits f pat = case pat of
  VarPat v -> VarPat v
  WildcardPat -> WildcardPat
  LitPat l -> f l
  ConPat c ps -> ConPat c (second (bindPatLits f) <$> ps)
  AnnoPat p t -> AnnoPat (bindPatLits f p) t
  ViewPat e p -> ViewPat e (bindPatLits f p)
  ForcedPat t -> ForcedPat t
  PatLoc loc p -> PatLoc loc (bindPatLits f p)

patternAbstraction
  :: (Eq b, Hashable b)
  => Vector b
  -> b
  -> Maybe PatternVar
patternAbstraction vs = fmap PatternVar . hashedElemIndex vs

indexedPatterns
  :: (Traversable f, Bitraversable pat)
  => f (p, pat b t)
  -> f (p, pat PatternVar t)
indexedPatterns = flip evalState 0 . traverse (traverse $ bitraverse inc pure)
  where
    inc _ = do
      n <- get
      put $! n + 1
      pure n

renamePatterns
  :: (Traversable f, Bitraversable pat)
  => Vector v
  -> f (p, pat b t)
  -> f (p, pat v t)
renamePatterns vs pats
  = fmap (first (\(PatternVar v) -> vs Vector.! v)) <$> indexedPatterns pats

instantiatePattern
  :: Monad f
  => (v -> f a)
  -> Vector v
  -> Scope PatternVar f a
  -> f a
instantiatePattern f vs
  = instantiate (f . fromMaybe (panic "instantiatePattern") . (vs Vector.!?) . unPatternVar)

-------------------------------------------------------------------------------
-- Instances
instance Bifunctor (Pat con lit) where bimap = bimapDefault
instance Bifoldable (Pat con lit) where bifoldMap = bifoldMapDefault

instance Bitraversable (Pat con lit) where
  bitraverse f g pat = case pat of
    VarPat b -> VarPat <$> f b
    WildcardPat -> pure WildcardPat
    LitPat l -> pure $ LitPat l
    ConPat c pats -> ConPat c <$> traverse (traverse (bitraverse f g)) pats
    AnnoPat p t -> AnnoPat <$> bitraverse f g p <*> g t
    ViewPat t p -> ViewPat <$> g t <*> bitraverse f g p
    ForcedPat t -> ForcedPat <$> g t
    PatLoc loc p -> PatLoc loc <$> bitraverse f g p

prettyPattern
  :: (Pretty con, Pretty lit, Pretty typ)
  => Vector Name
  -> Pat con lit b typ
  -> PrettyDoc
prettyPattern names = prettyM . first ((names Vector.!) . fst) . firstIndexed

instance (Pretty con, Pretty lit, Pretty typ, Pretty b) => Pretty (Pat con lit b typ) where
  prettyM pat = case pat of
    VarPat b -> prettyM b
    WildcardPat -> "_"
    LitPat l -> prettyM l
    ConPat c args -> prettyApps (prettyM c) $ (\(p, arg) -> prettyAnnotation p $ prettyM arg) <$> args
    AnnoPat p t -> parens `above` annoPrec $
      prettyM p <+> ":" <+> prettyM t
    ViewPat t p -> parens `above` arrPrec $
      prettyM t <+> "->" <+> prettyM p
    ForcedPat t -> prettyTightApp "~" $ prettyM t
    PatLoc _ p -> prettyM p

deriveEq1 ''Pat
deriveOrd1 ''Pat
deriveShow1 ''Pat
