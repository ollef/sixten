{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, OverloadedStrings, TypeSynonymInstances #-}
module Elaboration.Monad where

import Protolude

import Control.Monad.Except
import Control.Monad.Fail
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Elaboration.MetaVar
import MonadContext
import MonadFresh
import MonadLog
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Pre.Scoped as Pre
import TypedFreeVar
import Util
import Util.Tsil(Tsil)
import qualified Util.Tsil as Tsil
import VIX

type PreM = Pre.Expr FreeV
type CoreM = Core.Expr MetaVar FreeV

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
  { localVariables :: Tsil FreeV
  , elabTouchables :: !(MetaVar -> Bool)
  }

newtype Elaborate a = Elaborate (ReaderT ElabEnv VIX a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail, MonadFix, MonadError Error, MonadFresh, MonadReport, MonadLog, MonadVIX)

runElaborate :: Elaborate a -> VIX a
runElaborate (Elaborate i) = runReaderT i ElabEnv
  { localVariables = mempty
  , elabTouchables = const True
  }

instance MonadContext FreeV Elaborate where
  localVars = Elaborate $ asks localVariables

  inUpdatedContext f (Elaborate m) = Elaborate $ do
    vs <- asks localVariables
    let vs' = f vs
    logShow 30 "local variable scope" (varId <$> toList vs')
    indentLog $
      local
        (\env -> env { localVariables = vs' })
        m

exists
  :: NameHint
  -> Plicitness
  -> CoreM
  -> Elaborate CoreM
exists hint d typ = do
  locals <- toVector . Tsil.filter (isNothing . varValue) <$> localVars
  let typ' = Core.pis locals typ
  logMeta 30 "exists typ" typ
  let typ'' = close (panic "exists not closed") typ'
  loc <- currentLocation
  v <- explicitExists hint d typ'' (Vector.length locals) loc
  return $ Core.Meta v $ (\fv -> (varData fv, pure fv)) <$> locals

existsType
  :: NameHint
  -> Elaborate CoreM
existsType n = exists n Explicit Builtin.Type

getTouchable :: Elaborate (MetaVar -> Bool)
getTouchable = Elaborate $ asks elabTouchables

untouchable :: Elaborate a -> Elaborate a
untouchable (Elaborate i) = do
  v <- fresh
  Elaborate $ local (\s -> s { elabTouchables = \m -> elabTouchables s m && metaId m > v }) i
