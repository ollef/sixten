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
import Syntax.Annotation
import Syntax.Let
import Syntax.Name
import Syntax.NameHint
import Syntax.Telescope
import Util

data FreeVar e = FreeVar
  { varId :: !Int
  , varHint :: !NameHint
  , varPlicitness :: !Plicitness
  , varValue :: Maybe (IORef (Maybe (e (FreeVar e))))
  , varType :: e (FreeVar e)
  }

instance (Show1 e) => Show (FreeVar e) where
  showsPrec d (FreeVar i h p _ t) = showParen (d > 10) $
    showString "FreeVar" .
    showChar ' ' . showsPrec 11 i .
    showChar ' ' . showsPrec 11 h .
    showChar ' ' . showsPrec 11 p .
    showChar ' ' . showsPrec1 11 t

instance Eq (FreeVar e) where
  (==) = (==) `on` varId

instance Ord (FreeVar e) where
  compare = compare `on` varId

instance Hashable (FreeVar e) where
  hashWithSalt s = hashWithSalt s . varId

instance Pretty (FreeVar e) where
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
  -> Plicitness
  -> e (FreeVar e)
  -> m (FreeVar e)
freeVar h p t = do
  i <- fresh
  return $ FreeVar i h p Nothing t

-- | Like freeVar, but with logging. TODO merge with freeVar?
forall
  :: (MonadFresh m, MonadLog m)
  => NameHint
  -> Plicitness
  -> e (FreeVar e)
  -> m (FreeVar e)
forall h p t = do
  v <- freeVar h p t
  logCategory "forall" $ "forall: " <> shower (varId v)
  return v

extendContext
  :: (MonadFresh m, MonadLog m, MonadContext (FreeVar e) m)
  => NameHint
  -> Plicitness
  -> e (FreeVar e)
  -> (FreeVar e -> m a)
  -> m a
extendContext h p t k = do
  v <- forall h p t
  withVar v $ k v

teleExtendContext
  :: (MonadFresh m, MonadLog m, MonadContext (FreeVar e) m, Monad e)
  => Telescope e (FreeVar e)
  -> (Vector (FreeVar e) -> m a)
  -> m a
teleExtendContext tele k = do
  vs <- forTeleWithPrefixM tele $ \h p s vs -> do
    let e = instantiateTele pure vs s
    forall h p e
  withVars vs $ k vs

teleMapExtendContext
  :: (MonadFresh m, MonadLog m, MonadContext (FreeVar e') m, Monad e)
  => Telescope e (FreeVar e')
  -> (e (FreeVar e') -> m (e' (FreeVar e')))
  -> (Vector (FreeVar e') -> m a)
  -> m a
teleMapExtendContext tele f k = do
  vs <- forTeleWithPrefixM tele $ \h p s vs -> do
    let e = instantiateTele pure vs s
    e' <- withVars vs $ f e
    forall h p e'
  withVars vs $ k vs

letExtendContext
  :: (MonadFresh m, MonadLog m, MonadContext (FreeVar e) m)
  => LetRec e (FreeVar e)
  -> (Vector (FreeVar e) -> m a)
  -> m a
letExtendContext ds k = do
  vs <- forMLet ds $ \h _ _ t ->
    forall h Explicit t
  withVars vs $ k vs

letMapExtendContext
  :: (MonadFresh m, MonadLog m, MonadContext (FreeVar e') m)
  => LetRec e (FreeVar e')
  -> (e (FreeVar e') -> m (e' (FreeVar e')))
  -> (Vector (FreeVar e') -> m a)
  -> m a
letMapExtendContext tele f k = do
  vs <- forMLet tele $ \h _ _ t -> do
    t' <- f t
    forall h Explicit t'
  withVars vs $ k vs

letVar
  :: (MonadFresh m, MonadIO m)
  => NameHint
  -> e (FreeVar e)
  -> m (FreeVar e, e (FreeVar e) -> m ())
letVar h t = do
  i <- fresh
  ref <- liftIO $ newIORef Nothing
  return (FreeVar i h Explicit (Just ref) t, liftIO . writeIORef ref . Just)

showFreeVar
  :: (Functor e, Functor f, Foldable f, Pretty (f Doc), Pretty (e Doc))
  => f (FreeVar e)
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
  -> f (FreeVar e)
  -> m ()
logFreeVar c@(Category ct) s x = whenLoggingCategory c $ do
  let r = showFreeVar x
  Effect.log $ "[" <> ct <> "] " <> s <> ": " <> showWide r

varTelescope
  :: Monad e
  => Vector (FreeVar e)
  -> Telescope e (FreeVar e)
varTelescope vs
  = Telescope
  $ (\v -> TeleArg (varHint v) (varPlicitness v) $ abstract abstr $ varType v)
  <$> vs
  where
    abstr = teleAbstraction vs

varTypeTelescope
  :: Monad e'
  => Vector (FreeVar e, e' (FreeVar e))
  -> Telescope e' (FreeVar e)
varTypeTelescope vs
  = Telescope
  $ (\(v, t) -> TeleArg (varHint v) (varPlicitness v) $ abstract abstr t)
  <$> vs
  where
    abstr = teleAbstraction (fst <$> vs)
