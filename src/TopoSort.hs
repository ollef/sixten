module TopoSort where

import Data.Foldable
import Data.Graph

topoSort
  :: (Foldable t, Foldable t', Ord a)
  => t (a, t' a)
  -> [[a]]
topoSort
  = map flattenSCC
  . stronglyConnComp
  . fmap (\(k, xs) -> (k, k, toList xs))
  . toList
