module TopoSort where
import Data.List
import Data.Map(Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Set(Set)
import qualified Data.Set as S
-- import Test.QuickCheck
-- import Test.QuickCheck.Instances

fixPoint :: Eq a => (a -> a) -> a -> a
fixPoint f x | fx == x   = x
             | otherwise = fixPoint f fx
  where fx = f x

closure :: Ord a => Map a (Set a) -> Map a (Set a)
closure edges = fixPoint (fmap step) edges
  where step s = mconcat $ s : catMaybes [M.lookup a edges | a <- S.toList s]

subset :: (Ord a, Ord b) => Map a (Set b) -> Map a (Set b) -> Bool
subset = M.isSubmapOfBy S.isSubsetOf

{-
prop_closure_extensive :: Map Int (Set Int) -> Bool
prop_closure_extensive m = m `subset` closure m
prop_closure_increasing :: Map Int (Set Int) -> Map Int (Set Int) -> Property
prop_closure_increasing m n = m `subset` n ==> closure m `subset` closure n
prop_closure_idempotent :: Map Int (Set Int) -> Bool
prop_closure_idempotent m = closure (closure m) == closure m
-}

topoSort :: Ord a => Map a (Set a) -> [[a]]
topoSort edges = groupBy eq . insertionSort cmp $ M.keys edges
  where
    cedges = closure edges
    lt a b = S.member a (M.findWithDefault mempty b cedges)
    eq a b = lt a b && lt b a
    cmp a b | lt a b    = LT
            | otherwise = GT

    -- We use insertion sort because the ordering is not total
    insertionSort :: (a -> a -> Ordering) -> [a] -> [a]
    insertionSort _ []     = []
    insertionSort f (x:xs) = insertBy f x $ insertionSort f xs

{-
prop_topoSortCycle :: Map Int (Set Int) -> Bool
prop_topoSortCycle edges = all cyclicGroup xxs
  where
    cyclicGroup xs = and $ do
      x <- xs
      y <- xs
      return $ x == y || x `dependsOn` y
    x `dependsOn` y = S.member y (M.findWithDefault mempty x cedges)
    cedges         = closure edges
    xxs            = topoSort edges

prop_topoSortDeps :: Map Int (Set Int) -> Bool
prop_topoSortDeps edges = all correct $ concat xxs
  where
    cedges = closure edges
    correct x = all ((<= ix) . index) $ S.toList $ S.intersection deps (S.fromList $ M.keys edges)
      where
        ix = index x
        deps = M.findWithDefault mempty x cedges
    xxs = topoSort edges
    index i = fromMaybe (error "bad!") $ findIndex (i `elem`) xxs
-}

mmap :: (Ord a, Ord b) => [(a, [b])] -> Map a (Set b)
mmap xs = M.fromList [(a, S.fromList bs) | (a, bs) <- xs]
