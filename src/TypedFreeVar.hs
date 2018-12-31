{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module TypedFreeVar where

import Prelude(showsPrec, showParen, showString, showChar)
import Protolude

import Bound
import Data.Char
import Data.Functor.Classes
import qualified Data.HashSet as HashSet
import Data.IORef
import qualified Data.Text as Text
import Data.Vector(Vector)

import Effect
import Pretty
import Syntax.Name
import Syntax.NameHint
import Syntax.Telescope
import Util

data FreeVar d e = FreeVar
  { varId :: !Int
  , varHint :: !NameHint
  , varData :: d
  , varValue :: Maybe (IORef (Maybe (e (FreeVar d e))))
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

-- | Like freeVar, but with logging. TODO merge with freeVar?
forall
  :: (MonadFresh m, MonadLog m)
  => NameHint
  -> d
  -> e (FreeVar d e)
  -> m (FreeVar d e)
forall h p t = do
  v <- freeVar h p t
  logCategory "forall" $ "forall: " <> shower (varId v)
  return v

extendContext
  :: (MonadFresh m, MonadLog m, MonadContext (FreeVar d e) m)
  => NameHint
  -> d
  -> e (FreeVar d e)
  -> (FreeVar d e -> m a)
  -> m a
extendContext h p t k = do
  v <- forall h p t
  withVar v $ k v

teleExtendContext
  :: (MonadFresh m, MonadLog m, MonadContext (FreeVar d e) m, Monad e)
  => Telescope d e (FreeVar d e)
  -> (Vector (FreeVar d e) -> m a)
  -> m a
teleExtendContext tele k = do
  vs <- forTeleWithPrefixM tele $ \h p s vs -> do
    let e = instantiateTele pure vs s
    forall h p e
  withVars vs $ k vs

teleMapExtendContext
  :: (MonadFresh m, MonadLog m, MonadContext (FreeVar d e') m, Monad e)
  => Telescope d e (FreeVar d e')
  -> (e (FreeVar d e') -> m (e' (FreeVar d e')))
  -> (Vector (FreeVar d e') -> m a)
  -> m a
teleMapExtendContext tele f k = do
  vs <- forTeleWithPrefixM tele $ \h p s vs -> do
    let e = instantiateTele pure vs s
    e' <- withVars vs $ f e
    forall h p e'
  withVars vs $ k vs

letVar
  :: (MonadFresh m, MonadIO m)
  => NameHint
  -> d
  -> e (FreeVar d e)
  -> m (FreeVar d e, e (FreeVar d e) -> m ())
letVar h d t = do
  i <- fresh
  ref <- liftIO $ newIORef Nothing
  return (FreeVar i h d (Just ref) t, liftIO . writeIORef ref . Just)

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
  :: (Functor e, Functor f, Foldable f, Pretty (f Doc), Pretty (e Doc), MonadLog m)
  => Category
  -> Text
  -> f (FreeVar d e)
  -> m ()
logFreeVar c@(Category ct) s x = whenLoggingCategory c $ do
  let r = showFreeVar x
  Effect.log $ "[" <> ct <> "] " <> s <> ": " <> showWide r

varTelescope
  :: Monad e
  => Vector (FreeVar d e)
  -> Telescope d e (FreeVar d e)
varTelescope vs
  = Telescope
  $ (\v -> TeleArg (varHint v) (varData v) $ abstract abstr $ varType v)
  <$> vs
  where
    abstr = teleAbstraction vs

varTypeTelescope
  :: Monad e'
  => Vector (FreeVar d e, e' (FreeVar d e))
  -> Telescope () e' (FreeVar d e)
varTypeTelescope vs
  = Telescope
  $ (\(v, t) -> TeleArg (varHint v) () $ abstract abstr t)
  <$> vs
  where
    abstr = teleAbstraction (fst <$> vs)
