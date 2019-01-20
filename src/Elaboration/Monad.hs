{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Elaboration.Monad where

import Protolude

import Control.Lens hiding (Context)
import Control.Monad.Reader
import qualified Data.Vector as Vector
import Rock

import {-# SOURCE #-} Elaboration.MetaVar.Zonk
import qualified Builtin.Names as Builtin
import Driver.Query
import Effect
import qualified Effect.Context as Context
import Elaboration.MetaVar
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Pre.Scoped as Pre
import Util
import qualified Util.Tsil as Tsil
import VIX

type PreM = Pre.Expr FreeVar
type CoreM = Core.Expr MetaVar FreeVar

type Polytype = CoreM
type Rhotype = CoreM -- No top-level foralls

newtype InstUntil = InstUntil Plicitness
  deriving (Eq, Ord, Show)

shouldInst :: Plicitness -> InstUntil -> Bool
shouldInst Explicit _ = False
shouldInst _ (InstUntil Explicit) = True
shouldInst p (InstUntil p') | p == p' = False
shouldInst _ _ = True

data ElabEnv = ElabEnv
  { _context :: !(Context CoreM)
  , _elabTouchables :: !(MetaVar -> Bool)
  , _currentModule :: !ModuleName
  , _vixEnv :: !VIX.Env
  }

makeLenses ''ElabEnv

instance HasLogEnv ElabEnv where
  logEnv = vixEnv.logEnv

instance HasReportEnv ElabEnv where
  reportEnv = vixEnv.reportEnv

instance HasFreshEnv ElabEnv where
  freshEnv = vixEnv.freshEnv

instance HasContext CoreM ElabEnv where
  context = Elaboration.Monad.context

type Elaborate = ReaderT ElabEnv (Sequential (Task Query))

runElaborate :: ModuleName -> Elaborate a -> VIX a
runElaborate mname = withReaderT $ \env -> ElabEnv
  { _context = mempty
  , _elabTouchables = const True
  , _currentModule = mname
  , _vixEnv = env
  }

type MonadElaborate m = (MonadContext CoreM m, MonadLog m, MonadIO m, MonadReport m, MonadFresh m, MonadFetch Query m, MonadReader ElabEnv m)

exists
  :: MonadElaborate m
  => NameHint
  -> Plicitness
  -> CoreM
  -> m CoreM
exists hint d typ = do
  ctx <- getContext
  let
    locals = toVector $ Tsil.filter (isNothing . (`Context.lookupValue` ctx)) $ Context._vars ctx
  typ' <- Core.pis locals typ
  logMeta "tc.metavar" "exists typ" $ zonk typ
  let typ'' = close (panic "exists not closed") typ'
  loc <- getCurrentLocation
  v <- explicitExists hint d typ'' (Vector.length locals) loc
  return $ Core.Meta v $ (\fv -> (Context.lookupPlicitness fv ctx, pure fv)) <$> locals

existsType
  :: NameHint
  -> Elaborate CoreM
existsType n = exists n Explicit Builtin.Type

getTouchable :: MonadReader ElabEnv m => m (MetaVar -> Bool)
getTouchable = view elabTouchables

untouchable :: (MonadReader ElabEnv m, MonadFresh m) => m a -> m a
untouchable i = do
  v <- fresh
  local (over elabTouchables $ \t m -> t m && metaId m > v) i
