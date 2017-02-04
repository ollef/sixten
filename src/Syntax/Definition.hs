{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GADTs, Rank2Types, OverloadedStrings #-}
module Syntax.Definition where

import Bound
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import Data.Hashable
import qualified Data.HashMap.Lazy as HashMap
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

traverseDefinitionFirst
  :: (Bitraversable expr, Applicative f)
  => (a -> f a')
  -> Definition (expr a) v
  -> f (Definition (expr a') v)
traverseDefinitionFirst f (Definition d) = Definition <$> bitraverse f pure d
traverseDefinitionFirst f (DataDefinition d) = DataDefinition <$> traverseDataDefFirst f d

definitionFirst
  :: Bifunctor expr
  => (a -> a')
  -> Definition (expr a) v
  -> Definition (expr a') v
definitionFirst f (Definition d) = Definition $ first f d
definitionFirst f (DataDefinition d) = DataDefinition $ dataDefFirst f d

prettyTypedDef
  :: (Eq1 expr, Eq v, IsString v, Monad expr, Pretty (expr v), Syntax expr, Eq (Annotation expr), PrettyAnnotation (Annotation expr))
  => Definition expr v
  -> expr v
  -> PrettyM Doc
prettyTypedDef (Definition d) _ = prettyM d
prettyTypedDef (DataDefinition d) t = prettyDataDef (telescope t) d

abstractDef
  :: Monad expr
  => (a -> Maybe b)
  -> Definition expr a
  -> Definition expr (Var b a)
abstractDef f (Definition d) = Definition $ fromScope $ abstract f d
abstractDef f (DataDefinition d) = DataDefinition $ abstractDataDef f d

instantiateDef
  :: Monad expr
  => (b -> expr a)
  -> Definition expr (Var b a)
  -> Definition expr a
instantiateDef f (Definition d) = Definition $ instantiate f $ toScope d
instantiateDef f (DataDefinition d) = DataDefinition $ instantiateDataDef f d

instance (Monad expr, Pretty (expr v), IsString v) => Pretty (Definition expr v) where
  prettyM (Definition e) = prettyM e
  prettyM (DataDefinition d) = prettyM d

recursiveAbstractDefs
  :: (Eq v, Monad f, Functor t, Foldable t, Hashable v)
  => t (v, Definition f v)
  -> t (Definition f (Var Int v))
recursiveAbstractDefs es = (abstractDef (`HashMap.lookup` vs) . snd) <$> es
  where
    vs = HashMap.fromList $ zip (toList $ fst <$> es) [(0 :: Int)..]

foldMapDefinition
  :: (Monoid m, Monad expr)
  => (forall v. expr v -> m)
  -> Definition expr x
  -> m
foldMapDefinition f (Definition e) = f e
foldMapDefinition f (DataDefinition (DataDef cs)) = foldMap (foldMap $ f . fromScope) cs
