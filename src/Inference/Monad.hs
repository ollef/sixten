{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, OverloadedStrings, TypeSynonymInstances #-}
module Inference.Monad where

import Control.Monad.Except
import Control.Monad.Fail
import Control.Monad.Reader
import Data.Foldable
import Data.Maybe
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Inference.MetaVar
import MonadContext
import MonadFresh
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

data InferEnv = InferEnv
  { localVariables :: Tsil FreeV
  , inferTouchables :: !(MetaVar -> Bool)
  }

newtype Infer a = InferMonad (ReaderT InferEnv VIX a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail, MonadFix, MonadError Error, MonadFresh, MonadReport, MonadVIX)

runInfer :: Infer a -> VIX a
runInfer (InferMonad i) = runReaderT i InferEnv
  { localVariables = mempty
  , inferTouchables = const True
  }

instance MonadContext FreeV Infer where
  localVars = InferMonad $ asks localVariables

  inUpdatedContext f (InferMonad m) = InferMonad $ do
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
  -> Infer CoreM
exists hint d typ = do
  locals <- toVector . Tsil.filter (isNothing . varValue) <$> localVars
  let typ' = Core.pis locals typ
  logMeta 30 "exists typ" typ
  typ'' <- traverse (error "exists not closed") typ'
  loc <- currentLocation
  v <- explicitExists hint d typ'' (Vector.length locals) loc
  return $ Core.Meta v $ (\fv -> (varData fv, pure fv)) <$> locals

existsType
  :: NameHint
  -> Infer CoreM
existsType n = exists n Explicit Builtin.Type

getTouchable :: Infer (MetaVar -> Bool)
getTouchable = InferMonad $ asks inferTouchables

untouchable :: Infer a -> Infer a
untouchable (InferMonad i) = do
  v <- fresh
  InferMonad $ local (\s -> s { inferTouchables = \m -> inferTouchables s m && metaId m > v }) i
