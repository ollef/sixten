{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module FreeVar where

import Protolude

import Bound
import Data.Vector(Vector)

import Effect
import Pretty
import Syntax.Annotation
import Syntax.Name
import Syntax.NameHint
import Syntax.Telescope
import Util

data FreeVar d = FreeVar
  { varId :: !Int
  , varHint :: !NameHint
  , varPlicitness :: !Plicitness
  , varData :: d
  } deriving Show

instance Eq (FreeVar d) where
  (==) = (==) `on` varId

instance Ord (FreeVar d) where
  compare = compare `on` varId

instance Hashable (FreeVar d) where
  hashWithSalt s = hashWithSalt s . varId

instance Pretty (FreeVar d) where
  pretty (FreeVar i h _ _) = "$" <> shower i <> fromNameHint mempty fromName h

freeVar
  :: MonadFresh m
  => NameHint
  -> Plicitness
  -> d
  -> m (FreeVar d)
freeVar h p d = do
  i <- fresh
  return $ FreeVar i h p d

varTelescope
  :: Monad e
  => Vector (FreeVar d, e (FreeVar d))
  -> Telescope e (FreeVar d)
varTelescope vs
  = Telescope
  $ (\(v, t) -> TeleArg (varHint v) (varPlicitness v) $ abstract abstr t)
  <$> vs
  where
    abstr = teleAbstraction (fst <$> vs)
