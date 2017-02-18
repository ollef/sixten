{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GADTs, Rank2Types, OverloadedStrings #-}
module Syntax.Definition where

import Bound
import Data.Bifunctor
import Data.Bitraversable
import Data.String
import Prelude.Extras

import Pretty
import Syntax.Annotation
import Syntax.Class
import Syntax.Data
import Syntax.GlobalBind

data Definition expr v
  = Definition (expr v)
  | DataDefinition (DataDef expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance GlobalBound Definition where
  bound f g (Definition e) = Definition $ bind f g e
  bound f g (DataDefinition d) = DataDefinition $ bound f g d

bimapDefinition
  :: Bifunctor expr
  => (a -> a')
  -> (b -> b')
  -> Definition (expr a) b
  -> Definition (expr a') b'
bimapDefinition f g (Definition d) = Definition $ bimap f g d
bimapDefinition f g (DataDefinition d) = DataDefinition $ bimapDataDef f g d

bitraverseDefinition
  :: (Bitraversable expr, Applicative f)
  => (a -> f a')
  -> (b -> f b')
  -> Definition (expr a) b
  -> f (Definition (expr a') b')
bitraverseDefinition f g (Definition d) = Definition <$> bitraverse f g d
bitraverseDefinition f g (DataDefinition d) = DataDefinition <$> bitraverseDataDef f g d

prettyTypedDef
  :: (Eq1 expr, Eq v, IsString v, Monad expr, Pretty (expr v), Syntax expr, Eq (Annotation expr), PrettyAnnotation (Annotation expr))
  => Definition expr v
  -> expr v
  -> PrettyM Doc
prettyTypedDef (Definition d) _ = prettyM d
prettyTypedDef (DataDefinition d) t = prettyDataDef (telescope t) d

instance (Monad expr, Pretty (expr v), IsString v) => Pretty (Definition expr v) where
  prettyM (Definition e) = prettyM e
  prettyM (DataDefinition d) = prettyM d

foldMapDefinition
  :: (Monoid m, Monad expr)
  => (forall v. expr v -> m)
  -> Definition expr x
  -> m
foldMapDefinition f (Definition e) = f e
foldMapDefinition f (DataDefinition (DataDef cs)) = foldMap (foldMap $ f . fromScope) cs
