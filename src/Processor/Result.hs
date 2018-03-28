{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Processor.Result where

import Control.Monad
import Data.Semigroup as Semigroup
import Error

data Result a
  = Failure [Error]
  | Success a
  deriving (Show, Functor, Foldable, Traversable)

instance Semigroup a => Semigroup (Result a) where
  Failure es1 <> Failure es2 = Failure $ es1 Semigroup.<> es2
  Failure es1 <> _ = Failure es1
  _ <> Failure es2 = Failure es2
  Success a <> Success b = Success (a Semigroup.<> b)

instance Applicative Result where
  pure = Success
  Failure errs1 <*> Failure errs2 = Failure $ errs1 ++ errs2
  r1 <*> r2 = ap r1 r2

instance Monad Result where
  return = Success
  Failure errs >>= _ = Failure errs
  Success a >>= f = f a
