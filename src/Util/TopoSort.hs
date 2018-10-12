module Util.TopoSort
  ( topoSortWith
  , topoSort
  , cycles
  , SCC(..)
  , flattenSCC
  ) where

import Protolude

import Data.Graph

topoSortWith
  :: (Foldable t, Foldable t', Ord name)
  => (a -> name)
  -> (a -> t' name)
  -> t a
  -> [SCC a]
topoSortWith name deps as
  = stronglyConnComp [(a, name a, toList $ deps a) | a <- toList as]

topoSort
  :: (Foldable t, Foldable t', Ord a)
  => t (a, t' a)
  -> [SCC a]
topoSort xs = stronglyConnComp [(k, k, toList ys) | (k, ys) <- toList xs]

cycles
  :: (Foldable t, Foldable t', Ord a)
  => t (a, t' a)
  -> [[a]]
cycles xs = concatMap cyclicGroup (topoSort xs)
  where
    cyclicGroup (CyclicSCC ys) = [ys]
    cyclicGroup (AcyclicSCC _) = []
