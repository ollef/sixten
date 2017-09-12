{-# LANGUAGE DeriveFunctor, Rank2Types #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Util where

import Bound
import Bound.Var
import Control.Applicative
import Control.Monad.State
import Data.Bifoldable
import Data.Bifunctor
import Data.Bits
import Data.Foldable
import Data.Hashable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.List.NonEmpty(NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.Set(Set)
import qualified Data.Set as Set
import Data.String
import Data.Text(Text)
import qualified Data.Text as Text
import Data.Vector(Vector)
import qualified Data.Vector as Vector

type Scope1 = Scope ()

unusedVar :: (Monad f, Traversable f) => f (Var b a) -> Maybe (f a)
unusedVar = traverse $ unvar (const Nothing) pure

unusedScope :: (Monad f, Traversable f) => Scope b f a -> Maybe (f a)
unusedScope = unusedVar . fromScope

abstractNone :: Monad f => f a -> Scope b f a
abstractNone = Scope . return . F

instantiate1 :: Monad f => f a -> Scope1 f a -> f a
instantiate1 = Bound.instantiate1

instantiateSome
  :: Monad f
  => (b -> f (Var b' a))
  -> Scope b f a
  -> Scope b' f a
instantiateSome f s
  = toScope $ fromScope s >>= unvar f (pure . pure)

toSet ::  (Ord a, Foldable f) => f a -> Set a
toSet = foldMap Set.singleton

toVector :: Foldable f => f a -> Vector a
toVector = Vector.fromList . toList

toHashSet ::  (Eq a, Foldable f, Hashable a) => f a -> HashSet a
toHashSet = foldMap HashSet.singleton

subst1 :: (Monad expr, Eq v) => v -> expr v -> expr v -> expr v
subst1 v e e' = e' >>= f
  where
    f i | i == v = e
        | otherwise = pure i

bimapScope
  :: Bifunctor f
  => (x -> x')
  -> (y -> y')
  -> Scope b (f x) y
  -> Scope b (f x') y'
bimapScope f g (Scope s) = Scope $ bimap f (fmap (bimap f g)) s

bifoldMapScope
  :: (Bifoldable expr, Monoid m)
  => (x -> m)
  -> (y -> m)
  -> Scope b (expr x) y -> m
bifoldMapScope f g (Scope s) = bifoldMap f (unvar mempty $ bifoldMap f g) s

fromText :: IsString a => Text -> a
fromText = fromString . Text.unpack

shower :: (Show a, IsString b) => a -> b
shower = fromString . show

indexed :: Traversable f => f a -> f (Int, a)
indexed x = evalState (traverse go x) 0
  where
    go a = do
      i <- get
      put $! i + 1
      return (i, a)

data Unit a = Unit
  deriving (Functor)

instance Applicative Unit where
  pure _ = Unit
  _ <*> _ = Unit

instance Monad Unit where
  return _ = Unit
  _ >>= _ = Unit

fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a

snd3 :: (a, b, c) -> b
snd3 (_, b, _) = b

thd3 :: (a, b, c) -> c
thd3 (_, _, c) = c

mapWithPrefix
  :: (v -> Vector v' -> v')
  -> Vector v
  -> Vector v'
mapWithPrefix f vs = result
  where
    result = Vector.imap (\i v -> f v $ Vector.take i result) vs

forWithPrefix
  :: Vector v
  -> (v -> Vector v' -> v')
  -> Vector v'
forWithPrefix = flip mapWithPrefix

mapWithPrefixM
  :: (Monad m, Foldable t)
  => (v -> Vector v' -> m v')
  -> t v
  -> m (Vector v')
mapWithPrefixM f
  = foldlM (\vs' v -> Vector.snoc vs' <$> f v vs') mempty

forWithPrefixM
  :: (Monad m, Foldable t)
  => t v
  -> (v -> Vector v' -> m v')
  -> m (Vector v')
forWithPrefixM = flip mapWithPrefixM

-- TODO make proper module
type MultiHashMap k v = HashMap k (HashSet v)

multiInsert
  :: (Eq k, Hashable k, Eq v, Hashable v)
  => k
  -> v
  -> MultiHashMap k v
  -> MultiHashMap k v
multiInsert k v = HashMap.insertWith HashSet.union k $ HashSet.singleton v

multiUnion
  :: (Eq k, Hashable k, Eq v, Hashable v)
  => MultiHashMap k v
  -> MultiHashMap k v
  -> MultiHashMap k v
multiUnion = HashMap.unionWith HashSet.union

multiUnions
  :: (Eq k, Hashable k, Eq v, Hashable v)
  => [MultiHashMap k v]
  -> MultiHashMap k v
multiUnions = foldl' multiUnion mempty

multiFromList
  :: (Eq k, Hashable k, Eq v, Hashable v)
  => [(k, v)]
  -> MultiHashMap k v
multiFromList = foldr (uncurry multiInsert) mempty

multiMap
  :: (Eq k, Hashable k, Eq v, Hashable v, Eq v', Hashable v')
  => (v -> v')
  -> MultiHashMap k v
  -> MultiHashMap k v'
multiMap = fmap . HashSet.map

multiMapMaybe
  :: (Eq k, Hashable k, Eq v, Hashable v, Eq v', Hashable v')
  => (v -> Maybe v')
  -> MultiHashMap k v
  -> MultiHashMap k v'
multiMapMaybe p
  = fmap
  $ HashSet.fromList
  . mapMaybe p
  . HashSet.toList

nonEmptySome :: Alternative f => f a -> f (NonEmpty a)
nonEmptySome p = (NonEmpty.:|) <$> p <*> many p

logBase2 :: FiniteBits b => b -> Int
logBase2 x = finiteBitSize x - 1 - countLeadingZeros x

hashedElemIndex
  :: (Eq a, Hashable a)
  => Vector a
  -> a
  -> Maybe Int
hashedElemIndex xs
  -- Just guessing the cutoff here
  | Vector.length xs <= 16 = flip Vector.elemIndex xs
  | otherwise = flip HashMap.lookup m
  where
    m = HashMap.fromList $ zip (Vector.toList xs) [0..]
