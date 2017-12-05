{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module TypedFreeVar where

import Control.Monad.IO.Class
import Control.Monad.State
import Data.Function
import Data.Functor.Classes
import Data.Hashable
import qualified Data.HashSet as HashSet
import Data.Monoid
import Data.String

import Pretty
import Syntax.NameHint
import Syntax.Name
import VIX

data FreeVar d = FreeVar
  { varId :: !Int
  , varHint :: !NameHint
  , varType :: d (FreeVar d)
  }

instance Show1 d => Show (FreeVar d) where
  showsPrec d (FreeVar i h t) = showParen (d > 10) $
    showString "FreeVar" . showChar ' ' . showsPrec 11 i .
    showChar ' ' . showsPrec 11 h . showChar ' ' . showsPrec1 11 t

instance Eq (FreeVar d) where
  (==) = (==) `on` varId

instance Ord (FreeVar d) where
  compare = compare `on` varId

instance Hashable (FreeVar d) where
  hashWithSalt s = hashWithSalt s . varId

freeVar
  :: (MonadVIX m, MonadIO m)
  => NameHint
  -> d (FreeVar d)
  -> m (FreeVar d)
freeVar h d = do
  i <- fresh
  return $ FreeVar i h d

showFreeVar
  :: (Functor d, Functor f, Foldable f, Pretty (f String), Pretty (d String))
  => f (FreeVar d)
  -> Doc
showFreeVar x = do
  let vs = foldMap HashSet.singleton x
  let showVar v = "$" ++ fromNameHint "" fromName (varHint v)
          ++ show (varId v)
  let shownVars = [(showVar v, pretty $ showVar <$> varType v) | v <- HashSet.toList vs]
  pretty (showVar <$> x)
    <> if null shownVars
      then mempty
      else text ", free vars: " <> pretty shownVars

logFreeVar
  :: (Functor d, Functor f, Foldable f, Pretty (f String), Pretty (d String), MonadVIX m, MonadIO m)
  => Int
  -> String
  -> f (FreeVar d)
  -> m ()
logFreeVar v s x = whenVerbose v $ do
  i <- gets vixIndent
  let r = showFreeVar x
  VIX.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide r
