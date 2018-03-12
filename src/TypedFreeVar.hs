{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module TypedFreeVar where

import Bound
import Control.Monad.IO.Class
import Control.Monad.State
import Data.Function
import Data.Functor.Classes
import Data.Hashable
import qualified Data.HashSet as HashSet
import Data.Monoid
import Data.String
import Data.Vector(Vector)

import Fresh
import Pretty
import Syntax.Name
import Syntax.NameHint
import Syntax.Telescope
import Util
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
  :: MonadFresh m
  => NameHint
  -> d (FreeVar d)
  -> m (FreeVar d)
freeVar h d = do
  i <- fresh
  return $ FreeVar i h d

showFreeVar
  :: (Functor d, Functor f, Foldable f, Pretty (f Doc), Pretty (d Doc))
  => f (FreeVar d)
  -> Doc
showFreeVar x = do
  let vs = foldMap HashSet.singleton x
  let showVar :: FreeVar d -> Doc
      showVar v = "$" <> fromNameHint "" fromName (varHint v)
          <> shower (varId v)
  let shownVars = [(showVar v, pretty $ showVar <$> varType v) | v <- HashSet.toList vs]
  pretty (showVar <$> x)
    <> if null shownVars
      then mempty
      else ", free vars: " <> pretty shownVars

logFreeVar
  :: (Functor d, Functor f, Foldable f, Pretty (f Doc), Pretty (d Doc), MonadVIX m, MonadIO m)
  => Int
  -> String
  -> f (FreeVar d)
  -> m ()
logFreeVar v s x = whenVerbose v $ do
  i <- liftVIX $ gets vixIndent
  let r = showFreeVar x
  VIX.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide r

varTelescope
  :: Monad e
  => Vector (a, FreeVar e)
  -> Telescope a e (FreeVar e)
varTelescope vs =
  Telescope
  $ (\(a, v) -> TeleArg (varHint v) a $ abstract abstr $ varType v)
  <$> vs
  where
    abstr = teleAbstraction $ snd <$> vs
