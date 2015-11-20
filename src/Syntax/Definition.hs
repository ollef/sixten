{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts #-}
module Syntax.Definition where

import Data.Foldable
import Data.Hashable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HM
import Data.String
import Data.Bitraversable
import Bound
import Prelude.Extras

import Syntax.Annotation
import Syntax.Data
import Syntax.Name
import Syntax.Pretty

data Definition d expr v
  = Definition (expr v)
  | DataDefinition (DataDef d expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance (Eq1 expr, Eq v, Eq d, HasRelevance d, HasPlicitness d, IsString v, Monad expr, Pretty (expr v)) => Pretty (Definition d expr v) where
  prettyM (Definition d) = prettyM d
  prettyM (DataDefinition d) = prettyM d

abstractDef :: Monad expr
            => (a -> Maybe b) -> Definition d expr a -> Definition d expr (Var b a)
abstractDef f (Definition d) = Definition $ fromScope $ abstract f d
abstractDef f (DataDefinition d) = DataDefinition $ abstractDataDef f d

instantiateDef :: Monad expr
               => (b -> expr a) -> Definition d expr (Var b a) -> Definition d expr a
instantiateDef f (Definition d) = Definition $ instantiate f $ toScope d
instantiateDef f (DataDefinition d) = DataDefinition $ instantiateDataDef f d

instance Bound (Definition d) where
  Definition d >>>= f = Definition $ d >>= f
  DataDefinition d >>>= f = DataDefinition $ d >>>= f

tritraverseDef :: (Applicative f, Bitraversable expr)
              => (d -> f d')
              -> (a -> f a')
              -> (b -> f b')
              -> Definition d (expr a) b
              -> f (Definition d' (expr a') b')
tritraverseDef _ f g (Definition d) = Definition <$> bitraverse f g d
tritraverseDef e f g (DataDefinition d) = DataDefinition <$> tritraverseDataDef e f g d

recursiveAbstractDefs :: (Eq v, Monad f, Functor t, Foldable t, Hashable v)
                      => t (v, Definition d f v) -> t (Definition d f (Var Int v))
recursiveAbstractDefs es = (abstractDef (`HM.lookup` vs) . snd) <$> es
  where
    vs = HM.fromList $ zip (toList $ fst <$> es) [(0 :: Int)..]

type Program d expr v = HashMap Name (Definition d expr v, expr v, d)
