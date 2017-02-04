{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, MonadComprehensions, OverloadedStrings #-}
module Syntax.Abstract.Pattern where

import Control.Monad
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Monoid
import qualified Data.Vector as Vector
import Data.Vector(Vector)

import Syntax
import Util

data Pat typ b
  = VarPat !NameHint b
  | WildcardPat
  | LitPat Literal
  | ConPat QConstr (Vector (Plicitness, Pat typ b, typ))
  | ViewPat typ (Pat typ b)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

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
    ConPat c pats -> ConPat c [(a, p >>= f, typ) | (a, p, typ) <- pats]
    ViewPat t p -> ViewPat t $ p >>= f

instance Bifunctor Pat where bimap = bimapDefault
instance Bifoldable Pat where bifoldMap = bifoldMapDefault

instance Bitraversable Pat where
  bitraverse f g pat = case pat of
    VarPat h b -> VarPat h <$> g b
    WildcardPat -> pure WildcardPat
    LitPat l -> pure $ LitPat l
    ConPat c pats -> ConPat c <$> traverse (bitraverse (bitraverse f g) f) pats
    ViewPat t p -> ViewPat <$> f t <*> bitraverse f g p

patternHint :: Pat typ b -> NameHint
patternHint (VarPat h _) = h
patternHint _ = mempty

data PatternType t
  = VarPatType
  | LitPatType
  | ConPatType
  | ViewPatType t
  deriving (Eq, Ord)

patternType :: Pat t b -> PatternType t
patternType VarPat {} = VarPatType
patternType WildcardPat = VarPatType
patternType LitPat {} = LitPatType
patternType ConPat {} = ConPatType
patternType (ViewPat t _) = ViewPatType t

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
    ConPat c args -> prettyApps (prettyM c) $ (\(p, arg, _typ) -> prettyAnnotation p $ prettyM arg) <$> args
    ViewPat t p -> parens `above` arrPrec $
      prettyM t <+> "->" <+> prettyM p
