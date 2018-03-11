{-# LANGUAGE FlexibleContexts #-}
module FreeVar where

import Data.Function
import Data.Hashable

import Fresh
import Syntax.NameHint

data FreeVar d = FreeVar
  { varId :: !Int
  , varHint :: !NameHint
  , varData :: d
  } deriving Show

instance Eq (FreeVar d) where
  (==) = (==) `on` varId

instance Ord (FreeVar d) where
  compare = compare `on` varId

instance Hashable (FreeVar d) where
  hashWithSalt s = hashWithSalt s . varId

freeVar
  :: MonadFresh m
  => NameHint
  -> d
  -> m (FreeVar d)
freeVar h d = do
  i <- fresh
  return $ FreeVar i h d
