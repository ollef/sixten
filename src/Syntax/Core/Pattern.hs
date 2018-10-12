{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, MonadComprehensions, OverloadedStrings #-}
module Syntax.Core.Pattern where

import Protolude

import Data.Bifoldable
import Data.Bitraversable
import Data.Functor.Classes
import qualified Data.Vector as Vector
import Data.Vector(Vector)

import Syntax
import Util

data Pat typ b
  = VarPat !NameHint b
  | LitPat Literal
  | ConPat
      QConstr
      (Vector (Plicitness, typ)) -- ^ Parameters
      (Vector (Plicitness, Pat typ b, typ))
  | ViewPat typ (Pat typ b)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

patEq :: (typ1 -> typ2 -> Bool) -> (a -> b -> Bool) -> Pat typ1 a -> Pat typ2 b -> Bool
patEq _ g (VarPat _ a) (VarPat _ b) = g a b
patEq _ _ (LitPat l1) (LitPat l2) = l1 == l2
patEq f g (ConPat qc1 ps1 as1) (ConPat qc2 ps2 as2)
  = qc1 == qc2
  && liftEq (\(p1, t1) (p2, t2) -> p1 == p2 && f t1 t2) ps1 ps2
  && liftEq (\(p1, pat1, t1) (p2, pat2, t2) -> p1 == p2 && patEq f g pat1 pat2 && f t1 t2) as1 as2
patEq f g (ViewPat t1 p1) (ViewPat t2 p2) = f t1 t2 && patEq f g p1 p2
patEq _ _ _ _ = False

instance Applicative (Pat typ) where
  pure = return
  (<*>) = ap

instance Monad (Pat typ) where
  return = VarPat mempty
  pat >>= f = case pat of
    VarPat h b -> case f b of
      VarPat h' b' -> VarPat (h' <> h) b'
      fb -> fb
    LitPat l -> LitPat l
    ConPat c ps pats -> ConPat c ps [(a, p >>= f, typ) | (a, p, typ) <- pats]
    ViewPat t p -> ViewPat t $ p >>= f

instance Bifunctor Pat where bimap = bimapDefault
instance Bifoldable Pat where bifoldMap = bifoldMapDefault

instance Bitraversable Pat where
  bitraverse f g pat = case pat of
    VarPat h b -> VarPat h <$> g b
    LitPat l -> pure $ LitPat l
    ConPat c ps pats -> ConPat c <$> traverse (traverse f) ps <*> traverse (bitraverse (bitraverse f g) f) pats
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
patternType LitPat {} = LitPatType
patternType ConPat {} = ConPatType
patternType (ViewPat t _) = ViewPatType t

prettyPattern
  :: Pretty typ
  => Vector Name
  -> Pat typ b
  -> PrettyDoc
prettyPattern names = prettyM . fmap ((names Vector.!) . fst) . indexed

instance (Pretty typ, Pretty b) => Pretty (Pat typ b) where
  prettyM pat = case pat of
    VarPat _ b -> prettyM b
    LitPat l -> prettyM l
    ConPat c ps args -> prettyApps (prettyM c)
      $ (\(p, e) -> prettyTightApp "~" $ prettyAnnotation p $ prettyM e) <$> ps
      <|> (\(p, arg, _typ) -> prettyAnnotation p $ prettyM arg) <$> args
    ViewPat t p -> parens `above` arrPrec $
      prettyM t <+> "->" <+> prettyM p
