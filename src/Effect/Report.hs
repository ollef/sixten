{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
module Effect.Report where

import Protolude hiding (TypeError)

import Control.Lens
import Control.Monad.Except
import Control.Monad.ListT
import Control.Monad.Trans.Maybe
import qualified Data.List.Class as ListT

import Error
import Pretty
import SourceLoc

class Monad m => MonadReport m where
  report :: Error -> m ()
  located :: SourceLoc -> m a -> m a
  getCurrentLocation :: m (Maybe SourceLoc)

  default report
    :: (MonadTrans t, MonadReport m1, m ~ t m1)
    => Error -> m ()
  report = lift . report

  default getCurrentLocation
    :: (MonadTrans t, MonadReport m1, m ~ t m1)
    => m (Maybe SourceLoc)
  getCurrentLocation = lift getCurrentLocation

reportLocated :: MonadReport m => Doc -> m ()
reportLocated x = do
  loc <- getCurrentLocation
  report $ TypeError x loc mempty

data ReportEnv = ReportEnv
  { _currentLocation :: !(Maybe SourceLoc)
  , _reportAction :: !(Error -> IO ())
  }

emptyReportEnv :: (Error -> IO ()) -> ReportEnv
emptyReportEnv = ReportEnv Nothing

makeLenses ''ReportEnv

class HasReportEnv env where
  reportEnv :: Lens' env ReportEnv

instance HasReportEnv ReportEnv where
  reportEnv = identity

instance (MonadIO m, HasReportEnv env) => MonadReport (ReaderT env m) where
  report e = do
    f <- view $ reportEnv.reportAction
    liftIO $ f e
  located = local . set (reportEnv.currentLocation) . Just
  getCurrentLocation = view $ reportEnv.currentLocation

------------------------------------------------------------------------------
-- mtl instances
-------------------------------------------------------------------------------
instance MonadReport m => MonadReport (StateT s m) where
  located loc (StateT s) = StateT $ located loc <$> s
instance MonadReport m => MonadReport (ListT m) where
  located loc (ListT mxs) = ListT $ do
    xs <- located loc mxs
    pure $ case xs of
      ListT.Nil -> ListT.Nil
      ListT.Cons x xs' -> ListT.Cons x $ located loc xs'
instance MonadReport m => MonadReport (ExceptT e m) where
  located loc (ExceptT m) = ExceptT $ located loc m
instance MonadReport m => MonadReport (MaybeT m) where
  located loc (MaybeT m) = MaybeT $ located loc m
