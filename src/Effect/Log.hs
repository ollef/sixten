{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
module Effect.Log where

import Protolude hiding (log)

import Control.Lens
import Control.Monad.Except
import Control.Monad.ListT(ListT(ListT))
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Writer

import qualified Pretty
import Pretty(Pretty, pretty)

newtype Category = Category Text
  deriving (Eq, Ord, Show, Hashable, IsString)

class Monad m => MonadLog m where
  getLogCategories :: m (Category -> Bool)
  log :: Text -> m ()
  indent :: m a -> m a

  default getLogCategories
    :: (MonadTrans t, MonadLog m1, m ~ t m1)
    => m (Category -> Bool)
  getLogCategories = lift getLogCategories

  default log
    :: (MonadTrans t, MonadLog m1, m ~ t m1)
    => Text -> m ()
  log = lift . log

logCategory :: MonadLog m => Category -> Text -> m ()
logCategory c@(Category ct) t = whenLoggingCategory c $ log $ "[" <> ct <> "] " <> t

whenLoggingCategory :: MonadLog m => Category -> m () -> m ()
whenLoggingCategory c m = do
  p <- getLogCategories
  when (p c) m

logPretty :: (MonadLog m, Pretty a) => Category -> Text -> m a -> m ()
logPretty c@(Category ct) s mx = whenLoggingCategory c $ do
  x <- mx
  log $ "[" <> ct <> "] " <> s <> ": " <> Pretty.showWide (pretty x)

logShow :: (MonadLog m, Show a) => Category -> Text -> a -> m ()
logShow c@(Category ct) s x = whenLoggingCategory c $
  log $ "[" <> ct <> "] " <> s <> ": " <> show x

data LogEnv = LogEnv
  { _logCategories :: !(Category -> Bool)
  , _logAction :: !(Text -> IO ())
  }

makeLenses ''LogEnv

class HasLogEnv env where
  logEnv :: Lens' env LogEnv

instance HasLogEnv LogEnv where
  logEnv = identity

instance (MonadIO m, HasLogEnv env) => MonadLog (ReaderT env m) where
  getLogCategories = view $ logEnv.logCategories
  log t = do
    f <- view $ logEnv.logAction
    liftIO $ f t
  indent = local
    $ over (logEnv . logAction)
    $ \f x -> f ("| " <> x)

instance Semigroup LogEnv where
  LogEnv c1 log1 <> LogEnv c2 log2 = LogEnv ((||) <$> c1 <*> c2) (\t -> log1 t *> log2 t)

instance Monoid LogEnv where
  mempty = LogEnv (const False) $ \_ -> pure ()

-------------------------------------------------------------------------------
-- mtl instances
-------------------------------------------------------------------------------
instance (Monoid w, MonadLog m) => MonadLog (WriterT w m) where
  indent (WriterT m) = WriterT $ indent m
instance MonadLog m => MonadLog (StateT s m) where
  indent (StateT s) = StateT $ indent <$> s
instance MonadLog m => MonadLog (IdentityT m) where
  indent (IdentityT m) = IdentityT $ indent m
instance MonadLog m => MonadLog (ExceptT e m) where
  indent (ExceptT m) = ExceptT $ indent m
instance MonadLog m => MonadLog (MaybeT m) where
  indent (MaybeT m) = MaybeT $ indent m
instance MonadLog m => MonadLog (ListT m) where
  indent (ListT m) = ListT $ indent m
