{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Util.MultiHashMap where

import Data.Bifunctor
import Data.Foldable
import Data.Hashable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Maybe as Maybe

newtype MultiHashMap k v = MultiHashMap { toMap :: HashMap k (HashSet v) }
  deriving (Monoid)

insert
  :: (Eq k, Hashable k, Eq v, Hashable v)
  => k
  -> v
  -> MultiHashMap k v
  -> MultiHashMap k v
insert k = inserts k . HashSet.singleton

inserts
  :: (Eq k, Hashable k, Eq v, Hashable v)
  => k
  -> HashSet v
  -> MultiHashMap k v
  -> MultiHashMap k v
inserts k vs (MultiHashMap m)
  = MultiHashMap
  $ HashMap.insertWith HashSet.union k vs m

lookup
  :: (Eq k, Hashable k, Eq v, Hashable v)
  => k
  -> MultiHashMap k v
  -> HashSet v
lookup k (MultiHashMap m) = HashMap.lookupDefault mempty k m

lookupDefault
  :: (Eq k, Hashable k, Eq v, Hashable v)
  => HashSet v
  -> k
  -> MultiHashMap k v
  -> HashSet v
lookupDefault d k (MultiHashMap m) = case HashMap.lookup k m of
  Nothing -> d
  Just s
    | HashSet.null s -> d
    | otherwise -> s

union
  :: (Eq k, Hashable k, Eq v, Hashable v)
  => MultiHashMap k v
  -> MultiHashMap k v
  -> MultiHashMap k v
union (MultiHashMap m1) (MultiHashMap m2)
  = MultiHashMap
  $ HashMap.unionWith HashSet.union m1 m2

unions
  :: (Eq k, Hashable k, Eq v, Hashable v)
  => [MultiHashMap k v]
  -> MultiHashMap k v
unions = foldl' union mempty

intersection
  :: (Eq k, Hashable k, Eq v, Hashable v)
  => MultiHashMap k v
  -> MultiHashMap k w
  -> MultiHashMap k v
intersection (MultiHashMap m1) (MultiHashMap m2) = MultiHashMap $ HashMap.intersection m1 m2

setIntersection
  :: (Eq k, Hashable k, Eq v, Hashable v)
  => MultiHashMap k v
  -> HashSet k
  -> MultiHashMap k v
setIntersection (MultiHashMap m1) s = MultiHashMap $ HashMap.intersection m1 $ HashSet.toMap s

fromList
  :: (Eq k, Hashable k, Eq v, Hashable v)
  => [(k, v)]
  -> MultiHashMap k v
fromList = foldr (uncurry insert) mempty

toList
  :: (Eq k, Hashable k, Eq v, Hashable v)
  => MultiHashMap k v
  -> [(k, v)]
toList m = [(k, v) | (k, s) <- toMultiList m, v <- HashSet.toList s]

fromMultiList
  :: (Eq k, Hashable k, Eq v, Hashable v)
  => [(k, HashSet v)]
  -> MultiHashMap k v
fromMultiList = foldr (uncurry inserts) mempty

toMultiList
  :: (Eq k, Hashable k, Eq v, Hashable v)
  => MultiHashMap k v
  -> [(k, HashSet v)]
toMultiList (MultiHashMap m) = HashMap.toList m

map
  :: (Eq k, Hashable k, Eq v, Hashable v, Eq v', Hashable v')
  => (v -> v')
  -> MultiHashMap k v
  -> MultiHashMap k v'
map f (MultiHashMap m)
  = MultiHashMap
  $ fmap (HashSet.map f) m

mapMaybe
  :: (Eq k, Hashable k, Eq v, Hashable v, Eq v', Hashable v')
  => (v -> Maybe v')
  -> MultiHashMap k v
  -> MultiHashMap k v'
mapMaybe p (MultiHashMap m)
  = MultiHashMap
  $ HashMap.mapMaybe (nothingWhenEmpty . Maybe.mapMaybe p . HashSet.toList) m
  where
    nothingWhenEmpty [] = Nothing
    nothingWhenEmpty xs = Just $ HashSet.fromList xs

mapKeys
  :: (Eq k, Hashable k, Eq k', Hashable k', Eq v, Hashable v)
  => (k -> k')
  -> MultiHashMap k v
  -> MultiHashMap k' v
mapKeys f = fromMultiList . Prelude.map (first f) . toMultiList
