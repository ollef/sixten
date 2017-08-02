module Util.TopoSort where

import Data.Foldable
import Data.Graph
import Data.Hashable
import qualified Data.HashMap.Lazy as HashMap

topoSortWith
  :: (Foldable t, Functor t, Foldable t', Hashable name, Ord name)
  => (a -> name)
  -> (a -> t' name)
  -> t a
  -> [[a]]
topoSortWith name deps as = (>>= fmap (nameMap HashMap.!)) $ topoSort $ (\a -> (name a, deps a)) <$> as
  where
    nameMap = foldl' (\m dat -> HashMap.insertWith (++) (name dat) [dat] m) mempty as

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
