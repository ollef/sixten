module TopoSort where

import Data.Foldable
import Data.Graph
{-
import Test.QuickCheck
import Test.QuickCheck.Instances
import Data.Map(Map)
import Data.Set(Set)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L
import Data.Maybe
-}

topoSort
  :: (Foldable t, Foldable t', Ord a)
  => t (a, t' a)
  -> [[a]]
topoSort
  = map flattenSCC
  . stronglyConnComp
  . fmap (\(k, xs) -> (k, k, toList xs))
  . toList

{-
fixPoint :: Eq a => (a -> a) -> a -> a
fixPoint f x | fx == x   = x
             | otherwise = fixPoint f fx
  where fx = f x

closure :: Ord a
        => Map a (Set a) -> Map a (Set a)
closure edges = fixPoint (fmap step) edges
  where step s = mconcat $ s : catMaybes [M.lookup a edges | a <- S.toList s]

prop_topoSortCycle :: Map Int (Set Int) -> Bool
prop_topoSortCycle edges = all cyclicGroup xxs
  where
    cyclicGroup xs = and $ do
      x <- xs
      y <- xs
      return $ x == y || x `dependsOn` y
    x `dependsOn` y = S.member y (M.findWithDefault mempty x cedges)
    cedges         = closure edges
    xxs            = topoSort $ M.mapWithKey (\k a -> (k, a)) edges

prop_topoSortDeps :: Map Int (Set Int) -> Bool
prop_topoSortDeps edges = all correct $ concat xxs
  where
    cedges = closure edges
    correct x = all ((<= ix) . index) $ S.toList $ S.intersection deps (S.fromList $ M.keys edges)
      where
        ix = index x
        deps = M.findWithDefault mempty x cedges
    xxs = topoSort $ M.mapWithKey (\k a -> (k, a)) edges
    index i = fromMaybe (error "bad!") $ L.findIndex (i `elem`) xxs
-}
