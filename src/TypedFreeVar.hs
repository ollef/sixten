{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module TypedFreeVar where

import Bound
import Control.Monad.IO.Class
import Control.Monad.State
import Data.Char
import Data.Function
import Data.Functor.Classes
import Data.Hashable
import qualified Data.HashSet as HashSet
import Data.Monoid
import Data.String
import qualified Data.Text as Text
import Data.Vector(Vector)

import MonadFresh
import Pretty
import Syntax.Name
import Syntax.NameHint
import Syntax.Telescope
import Util
import VIX

data FreeVar d e = FreeVar
  { varId :: !Int
  , varHint :: !NameHint
  , varData :: d
  , varValue :: Maybe (e (FreeVar d e))
  , varType :: e (FreeVar d e)
  }

instance (Show d, Show1 e) => Show (FreeVar d e) where
  showsPrec d (FreeVar i h p _ t) = showParen (d > 10) $
    showString "FreeVar" .
    showChar ' ' . showsPrec 11 i .
    showChar ' ' . showsPrec 11 h .
    showChar ' ' . showsPrec 11 p .
    showChar ' ' . showsPrec1 11 t

instance Eq (FreeVar d e) where
  (==) = (==) `on` varId

instance Ord (FreeVar d e) where
  compare = compare `on` varId

instance Hashable (FreeVar d e) where
  hashWithSalt s = hashWithSalt s . varId

instance Pretty (FreeVar d e) where
  pretty (FreeVar i h _ _ _)
    | Text.null hintText = "$" <> shower i
    | isDigit (Text.last hintText) = "$" <> hint <> "-" <> shower i
    | otherwise = "$" <> hint <> shower i
    where
      hintText = fromNameHint mempty fromName h
      hint = pretty hintText

freeVar
  :: MonadFresh m
  => NameHint
  -> d
  -> e (FreeVar d e)
  -> m (FreeVar d e)
freeVar h d t = do
  i <- fresh
  return $ FreeVar i h d Nothing t

letVar
  :: MonadFresh m
  => NameHint
  -> d
  -> e (FreeVar d e)
  -> e (FreeVar d e)
  -> m (FreeVar d e)
letVar h d e t = do
  i <- fresh
  return $ FreeVar i h d (Just e) t

-- | Like freeVar, but with logging
forall
  :: (MonadFresh m, MonadVIX m, MonadIO m)
  => NameHint
  -> d
  -> e (FreeVar d e)
  -> m (FreeVar d e)
forall h p t = do
  v <- freeVar h p t
  logVerbose 20 $ "forall: " <> shower (varId v)
  return v

showFreeVar
  :: (Functor e, Functor f, Foldable f, Pretty (f Doc), Pretty (e Doc))
  => f (FreeVar d e)
  -> Doc
showFreeVar x = do
  let vs = toHashSet x
  let shownVars = [(pretty v, pretty $ pretty <$> varType v) | v <- HashSet.toList vs]
  pretty (pretty <$> x)
    <> if null shownVars
      then mempty
      else ", free vars: " <> pretty shownVars

logFreeVar
  :: (Functor e, Functor f, Foldable f, Pretty (f Doc), Pretty (e Doc), MonadVIX m, MonadIO m)
  => Int
  -> String
  -> f (FreeVar d e)
  -> m ()
logFreeVar v s x = whenVerbose v $ do
  i <- liftVIX $ gets vixIndent
  let r = showFreeVar x
  VIX.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide r

varTelescope
  :: Monad e
  => Vector (FreeVar d e)
  -> Telescope d e (FreeVar d e)
varTelescope vs =
  Telescope
  $ (\v -> TeleArg (varHint v) (varData v) $ abstract abstr $ varType v)
  <$> vs
  where
    abstr = teleAbstraction vs

varTelescope'
  :: Monad e
  => Vector (d, FreeVar d' e)
  -> Telescope d e (FreeVar d' e)
varTelescope' vs =
  Telescope
  $ (\(d, v) -> TeleArg (varHint v) d $ abstract abstr $ varType v)
  <$> vs
  where
    abstr = teleAbstraction (snd <$> vs)
