{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
module Syntax.Definition where

import Protolude

import Bound
import Control.Monad.Morph
import Data.Bitraversable
import Data.Deriving
import Data.Functor.Classes
import Data.Hashable.Lifted

import Pretty
import Syntax.Annotation
import Syntax.Data
import Syntax.GlobalBind

data Definition expr v
  = ConstantDefinition Abstract (expr v)
  | DataDefinition (DataDef expr v) (expr v)
  deriving (Eq, Ord, Show, Foldable, Functor, Traversable, Generic, Hashable, Generic1, Hashable1)

newtype ClosedDefinition expr = ClosedDefinition { openDefinition :: forall a b. Definition (expr a) b }

instance (Hashable1 (expr Void), Monad (expr Void)) => Hashable (ClosedDefinition expr) where
  hashWithSalt s (ClosedDefinition d) =
    hashWithSalt1 s (d :: Definition (expr Void) Void)

instance (Eq1 (expr Void), Monad (expr Void)) => Eq (ClosedDefinition expr) where
  ClosedDefinition d1 == ClosedDefinition d2 =
    liftEq (==) (d1 :: Definition (expr Void) Void) d2

closeDefinition
  :: Bifunctor expr
  => (a -> Void)
  -> (b -> Void)
  -> Definition (expr a) b
  -> ClosedDefinition expr
closeDefinition f g def = ClosedDefinition $ bimapDefinition (absurd . f) (absurd . g) def

instance MFunctor Definition where
  hoist f (ConstantDefinition a e) = ConstantDefinition a $ f e
  hoist f (DataDefinition d e) = DataDefinition (hoist f d) (f e)

instance Bound Definition where
  ConstantDefinition a e >>>= f = ConstantDefinition a $ e >>= f
  DataDefinition d e >>>= f = DataDefinition (d >>>= f) (e >>= f)

instance GBound Definition where
  gbound f (ConstantDefinition a e) = ConstantDefinition a $ gbind f e
  gbound f (DataDefinition d e) = DataDefinition (gbound f d) (gbind f e)

bimapDefinition
  :: Bifunctor expr
  => (a -> a')
  -> (b -> b')
  -> Definition (expr a) b
  -> Definition (expr a') b'
bimapDefinition f g (ConstantDefinition a d) = ConstantDefinition a $ bimap f g d
bimapDefinition f g (DataDefinition d e) = DataDefinition (bimapDataDef f g d) (bimap f g e)

bitraverseDefinition
  :: (Bitraversable expr, Applicative f)
  => (a -> f a')
  -> (b -> f b')
  -> Definition (expr a) b
  -> f (Definition (expr a') b')
bitraverseDefinition f g (ConstantDefinition a d) = ConstantDefinition a <$> bitraverse f g d
bitraverseDefinition f g (DataDefinition d e) = DataDefinition <$> bitraverseDataDef f g d <*> bitraverse f g e

transverseDefinition
  :: (Traversable expr, Monad f)
  => (forall r. expr r -> f (expr' r))
  -> Definition expr a
  -> f (Definition expr' a)
transverseDefinition f (ConstantDefinition a e) = ConstantDefinition a <$> f e
transverseDefinition f (DataDefinition d t) = DataDefinition <$> transverseDataDef f d <*> f t

instance (Monad expr, Pretty (expr v), v ~ Doc, Eq1 expr) => PrettyNamed (Definition expr v) where
  prettyNamed name (ConstantDefinition a e) = prettyM a <$$> name <+> "=" <+> prettyM e
  prettyNamed name (DataDefinition d e) = prettyNamed name d <+> "=" <+> prettyM e

instance (Monad expr, Pretty (expr v), v ~ Doc, Eq1 expr) => Pretty (Definition expr v) where
  prettyM = prettyNamed "_"

return []

instance (Eq1 typ, Monad typ) => Eq1 (Definition typ) where
  liftEq = $(makeLiftEq ''Definition)
instance (Ord1 typ, Monad typ) => Ord1 (Definition typ) where
  liftCompare = $(makeLiftCompare ''Definition)
instance (Show1 typ, Monad typ) => Show1 (Definition typ) where
  liftShowsPrec = $(makeLiftShowsPrec ''Definition)
