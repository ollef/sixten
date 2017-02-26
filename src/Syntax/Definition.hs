{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GADTs, Rank2Types, OverloadedStrings #-}
module Syntax.Definition where

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
  | DataDefinition (DataDef expr v) (expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance GlobalBound Definition where
  bound f g (Definition e) = Definition $ bind f g e
  bound f g (DataDefinition d e) = DataDefinition (bound f g d) (bind f g e)

bimapDefinition
  :: Bifunctor expr
  => (a -> a')
  -> (b -> b')
  -> Definition (expr a) b
  -> Definition (expr a') b'
bimapDefinition f g (Definition d) = Definition $ bimap f g d
bimapDefinition f g (DataDefinition d e) = DataDefinition (bimapDataDef f g d) (bimap f g e)

bitraverseDefinition
  :: (Bitraversable expr, Applicative f)
  => (a -> f a')
  -> (b -> f b')
  -> Definition (expr a) b
  -> f (Definition (expr a') b')
bitraverseDefinition f g (Definition d) = Definition <$> bitraverse f g d
bitraverseDefinition f g (DataDefinition d e) = DataDefinition <$> bitraverseDataDef f g d <*> bitraverse f g e

prettyTypedDef
  :: (Eq1 expr, Eq v, IsString v, Monad expr, Pretty (expr v), Syntax expr, Eq (Annotation expr), PrettyAnnotation (Annotation expr))
  => Definition expr v
  -> expr v
  -> PrettyM Doc
prettyTypedDef (Definition d) _ = prettyM d
prettyTypedDef (DataDefinition d e) t = prettyDataDef (telescope t) d <+> "=" <+> prettyM e

instance (Monad expr, Pretty (expr v), IsString v) => Pretty (Definition expr v) where
  prettyM (Definition e) = prettyM e
  prettyM (DataDefinition d e) = prettyM d <+> "=" <+> prettyM e
