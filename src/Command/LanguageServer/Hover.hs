{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Command.LanguageServer.Hover where

import Protolude

import Control.Lens
import Control.Monad.ListT(ListT(ListT))
import qualified Data.List.Class as ListT
import Text.Parsix.Position

import Effect
import Syntax
import Syntax.Core
import TypedFreeVar

inside :: Int -> Int -> Span -> Bool
inside row column (Span start end)
  = row >= visualRow start
  && row <= visualRow end
  && (row /= visualRow start || column >= visualColumn start)
  && (row /= visualRow end || column < visualColumn end)

type FreeV = FreeVar Plicitness (Expr Void)

-- TODO check file as well

data HoverEnv = HoverEnv
  { _freshEnv :: !FreshEnv
  , _contextEnv :: !(ContextEnv FreeV)
  , _logEnv :: !LogEnv
  }

makeLenses ''HoverEnv

instance HasFreshEnv HoverEnv where
  freshEnv = Command.LanguageServer.Hover.freshEnv

instance HasContextEnv FreeV HoverEnv where
  contextEnv = Command.LanguageServer.Hover.contextEnv

instance HasLogEnv HoverEnv where
  logEnv = Command.LanguageServer.Hover.logEnv

newtype Hover a = Hover { unHover :: ListT (ReaderT HoverEnv IO) a }
  deriving (Functor, Applicative, Alternative, Monad, MonadIO, Semigroup, Monoid, MonadContext FreeV, MonadFresh, MonadLog)

instance MonadReader r m => MonadReader r (ListT m) where
  ask = ListT $ do
    x <- ask
    pure $ ListT.Cons x $ ListT $ pure ListT.Nil
  local f (ListT mxs) = ListT $ do
    xs <- local f mxs
    pure $ case xs of
      ListT.Cons x mxs' -> ListT.Cons x $ local f mxs'
      ListT.Nil -> ListT.Nil

runHover :: Hover a -> IO [a]
runHover (Hover m) = do
  f <- emptyFreshEnv
  let c = emptyContextEnv
      l = LogEnv
        { _logCategories = const False
        , _logAction = \_ -> return ()
        }
  runReaderT (ListT.toList m) (HoverEnv f c l)

emitCons :: a -> Hover a -> Hover a
emitCons a as
  = Hover $ ListT $ pure $ ListT.Cons a $ unHover as

hoverDefs
  :: (Span -> Bool)
  -> [(GName, SourceLoc, ClosedDefinition Expr, Biclosed Expr)]
  -> IO [(Span, Expr Void FreeV)]
hoverDefs f defs = runHover $ hoverClosedDef f =<< Hover (ListT.fromList defs)

hoverClosedDef
  :: (Span -> Bool)
  -> (GName, SourceLoc, ClosedDefinition Expr, Biclosed Expr)
  -> Hover (Span, Expr Void FreeV)
hoverClosedDef f (_, loc, ClosedDefinition def, Biclosed e) = do
  guard $ f $ sourceLocSpan loc
  hoverDef f def <> hoverExpr f e

hoverDef
  :: (Span -> Bool)
  -> Definition (Expr Void) FreeV
  -> Hover (Span, Expr Void FreeV)
hoverDef f (ConstantDefinition _ e) = hoverExpr f e
hoverDef f (DataDefinition (DataDef params cs) _rep) =
  teleExtendContext params $ \vs ->
    foldMap (hoverExpr f . varType) vs
    <> foldMap (\(ConstrDef _ s) -> hoverExpr f $ instantiateTele pure vs s) cs

hoverExpr
  :: (Span -> Bool)
  -> Expr Void FreeV
  -> Hover (Span, Expr Void FreeV)
hoverExpr f expr = case expr of
  Var _ -> mempty
  Meta m _ -> absurd m
  Global _ -> mempty
  Con _ -> mempty
  Lit _ -> mempty
  Pi h p t s ->
    extendContext h p t $ \v ->
      hoverExpr f t <> hoverExpr f (instantiate1 (pure v) s)
  Lam h p t s ->
    extendContext h p t $ \v ->
      hoverExpr f t <> hoverExpr f (instantiate1 (pure v) s)
  App e1 _ e2 -> hoverExpr f e1 <> hoverExpr f e2
  Let ds scope -> do
    vs <- forMLet ds $ \h _ _ t -> freeVar h Explicit t
    fold (forLet ds $ \_ loc s t -> do
        guard $ f $ sourceLocSpan loc
        hoverExpr f t <> withVars vs (hoverExpr f $ instantiateLet pure vs s))
      <> hoverExpr f (instantiateLet pure vs scope)
  Case e brs _ -> hoverExpr f e <> hoverBranches f brs
  ExternCode e _ -> fold $ hoverExpr f <$> e
  SourceLoc loc e -> do
    guard $ f $ sourceLocSpan loc
    emitCons (sourceLocSpan loc, e) $ hoverExpr f e

hoverBranches
  :: (Span -> Bool)
  -> Branches Plicitness (Expr Void) FreeV
  -> Hover (Span, Expr Void FreeV)
hoverBranches f (LitBranches lbrs def) =
  foldMap (\(LitBranch _ e) -> hoverExpr f e) lbrs
  <> hoverExpr f def
hoverBranches f (ConBranches cbrs) =
  flip foldMap cbrs $ \(ConBranch _ tele scope) ->
    teleExtendContext tele $ \vs ->
      foldMap (hoverExpr f . varType) vs
      <> hoverExpr f (instantiateTele pure vs scope)
