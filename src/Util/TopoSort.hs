module Util.TopoSort where

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

cycles
  :: (Foldable t, Foldable t', Ord a)
  => t (a, t' a)
  -> [[a]]
cycles xs = selfCycles ++ concatMap cyclicGroup (topoSort xs)
  where
    selfCycles = (\(a, _) -> [a]) <$> filter (uncurry elem) (toList xs)
    cyclicGroup ys@(_:_:_) = [ys]
    cyclicGroup _ = []
