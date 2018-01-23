{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GADTs, Rank2Types, OverloadedStrings #-}
module Syntax.Definition where

import Control.Monad.Morph
import Data.Bifunctor
import Data.Bitraversable

import Pretty
import Syntax.Annotation
import Syntax.Data
import Syntax.GlobalBind

data Definition expr v
  = Definition Abstract IsInstance (expr v)
  | DataDefinition (DataDef expr v) (expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance MFunctor Definition where
  hoist f (Definition a i e) = Definition a i $ f e
  hoist f (DataDefinition d e) = DataDefinition (hoist f d) (f e)

instance GlobalBound Definition where
  bound f g (Definition a i e) = Definition a i $ bind f g e
  bound f g (DataDefinition d e) = DataDefinition (bound f g d) (bind f g e)

bimapDefinition
  :: Bifunctor expr
  => (a -> a')
  -> (b -> b')
  -> Definition (expr a) b
  -> Definition (expr a') b'
bimapDefinition f g (Definition a i d) = Definition a i $ bimap f g d
bimapDefinition f g (DataDefinition d e) = DataDefinition (bimapDataDef f g d) (bimap f g e)

bitraverseDefinition
  :: (Bitraversable expr, Applicative f)
  => (a -> f a')
  -> (b -> f b')
  -> Definition (expr a) b
  -> f (Definition (expr a') b')
bitraverseDefinition f g (Definition a i d) = Definition a i <$> bitraverse f g d
bitraverseDefinition f g (DataDefinition d e) = DataDefinition <$> bitraverseDataDef f g d <*> bitraverse f g e

instance (Monad expr, Pretty (expr v), v ~ Doc) => PrettyNamed (Definition expr v) where
  prettyNamed name (Definition a i e) = prettyM a <+> prettyM i <$$> name <+> "=" <+> prettyM e
  prettyNamed name (DataDefinition d e) = prettyNamed name d <+> "=" <+> prettyM e

instance (Monad expr, Pretty (expr v), v ~ Doc) => Pretty (Definition expr v) where
  prettyM = prettyNamed "_"
