{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GADTs, Rank2Types, OverloadedStrings #-}
module Syntax.Definition where

import Control.Monad.Morph
import Data.Bifunctor
import Data.Bitraversable
import Data.String

import Pretty
import Syntax.Annotation
import Syntax.Data
import Syntax.GlobalBind

data Definition expr v
  = Definition Abstract (expr v)
  | DataDefinition (DataDef expr v) (expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance MFunctor Definition where
  hoist f (Definition a e) = Definition a $ f e
  hoist f (DataDefinition d e) = DataDefinition (hoist f d) (f e)

instance GlobalBound Definition where
  bound f g (Definition a e) = Definition a $ bind f g e
  bound f g (DataDefinition d e) = DataDefinition (bound f g d) (bind f g e)

bimapDefinition
  :: Bifunctor expr
  => (a -> a')
  -> (b -> b')
  -> Definition (expr a) b
  -> Definition (expr a') b'
bimapDefinition f g (Definition a d) = Definition a $ bimap f g d
bimapDefinition f g (DataDefinition d e) = DataDefinition (bimapDataDef f g d) (bimap f g e)

bitraverseDefinition
  :: (Bitraversable expr, Applicative f)
  => (a -> f a')
  -> (b -> f b')
  -> Definition (expr a) b
  -> f (Definition (expr a') b')
bitraverseDefinition f g (Definition a d) = Definition a <$> bitraverse f g d
bitraverseDefinition f g (DataDefinition d e) = DataDefinition <$> bitraverseDataDef f g d <*> bitraverse f g e

instance (Monad expr, Pretty (expr v), IsString v) => PrettyNamed (Definition expr v) where
  prettyNamed name (Definition a e) = name <+> "=" <+> prettyM a <+> prettyM e
  prettyNamed name (DataDefinition d e) = prettyNamed name d <+> "=" <+> prettyM e

instance (Monad expr, Pretty (expr v), IsString v) => Pretty (Definition expr v) where
  prettyM = prettyNamed "_"
