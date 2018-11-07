{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module VIX(Env(..), VIX, runVIX, hoistIO) where

import Protolude hiding (TypeError)

import Control.Lens
import Control.Monad.Morph
import Rock

import Driver.Query
import Effect.Fresh
import Effect.Log
import Effect.Report

data Env = Env
  { _logEnv :: !LogEnv
  , _reportEnv :: !ReportEnv
  , _freshEnv :: !FreshEnv
  }

makeLenses ''Env

type VIX = ReaderT Env (Sequential (Task Query))

runVIX :: LogEnv -> ReportEnv -> VIX a -> Task Query a
runVIX logEnv_ reportEnv_ vix = do
  freshEnv_ <- liftIO emptyFreshEnv
  runSequential $ runReaderT vix Env
    { _logEnv = logEnv_
    , _reportEnv = reportEnv_
    , _freshEnv = freshEnv_
    }

instance HasLogEnv Env where logEnv = VIX.logEnv
instance HasReportEnv Env where reportEnv = VIX.reportEnv
instance HasFreshEnv Env where freshEnv = VIX.freshEnv

hoistIO :: ReaderT Env IO a -> VIX a
hoistIO = hoist liftIO
