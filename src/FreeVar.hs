{-# LANGUAGE FlexibleContexts #-}
module FreeVar where

import Control.Monad.IO.Class
import Data.Function
import Data.Hashable

import Syntax.NameHint
import VIX

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
  :: (MonadVIX m, MonadIO m)
  => NameHint
  -> d
  -> m (FreeVar d)
freeVar h d = do
  i <- fresh
  return $ FreeVar i h d
