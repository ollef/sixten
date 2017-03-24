{-# LANGUAGE RankNTypes #-}
module Transversable where

import Bound.Scope

class Transversable t where
  transverse
    :: (Applicative f, Traversable g)
    => (forall x. g x -> f (h x))
    -> t g a
    -> f (t h a)

instance Transversable (Scope b) where
  transverse = transverseScope
