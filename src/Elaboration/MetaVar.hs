{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Elaboration.MetaVar where

import Prelude(showsPrec, showString, showChar, showParen)
import Protolude

import Data.Bitraversable
import Data.IORef
import Data.String
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Effect
import qualified Effect.Context as Context
import Syntax
import Syntax.Core
import Util
import qualified Util.Tsil as Tsil

type MetaRef = IORef (Maybe (Closed (Expr MetaVar)))

data MetaVar = MetaVar
  { metaId :: !Int
  , metaType :: Closed (Expr MetaVar)
  , metaArity :: !Int
  , metaHint :: !NameHint
  , metaPlicitness :: !Plicitness
  , metaSourceLoc :: !(Maybe SourceLoc)
  , metaRef :: !MetaRef
  }

instance Eq MetaVar where
  (==) = (==) `on` metaId

instance Ord MetaVar where
  compare = compare `on` metaId

instance Hashable MetaVar where
  hashWithSalt s = hashWithSalt s . metaId

instance Show MetaVar where
  showsPrec d (MetaVar i (Closed t) a h p _ _) = showParen (d > 10) $
    showString "MetaVar" . showChar ' ' .
    showsPrec 11 i . showChar ' ' .
    showsPrec 11 (t :: Expr MetaVar Void) . showChar ' ' .
    showsPrec 11 a . showChar ' ' .
    showsPrec 11 h . showChar ' ' .
    showsPrec 11 p . showChar ' ' .
    showString "<Ref>"

explicitExists
  :: (MonadContext e m, MonadLog m, MonadIO m, MonadFresh m)
  => NameHint
  -> Plicitness
  -> Closed (Expr MetaVar)
  -> Int
  -> Maybe SourceLoc
  -> m MetaVar
explicitExists hint p typ a loc = do
  i <- fresh
  ref <- liftIO $ newIORef Nothing
  logCategory "tc.metavar" $ "exists: " <> shower i
  logMeta "tc.metavar" "explicit exists typ" $ pure $ open typ
  return $ MetaVar i typ a hint p loc ref

solution
  :: MonadIO m
  => MetaVar
  -> m (Maybe (Closed (Expr MetaVar)))
solution m = do
  res <- liftIO $ readIORef $ metaRef m
  case res of
    Just (Closed (Meta m' (Mempty :: Vector (Plicitness, Expr MetaVar Void)))) -> do
      mres' <- solution m'
      case mres' of
        Nothing -> return res
        Just res' -> do
          -- Path compression
          solve m res'
          return mres'
    _ -> return res

solve
  :: MonadIO m
  => MetaVar
  -> Closed (Expr MetaVar)
  -> m ()
solve m x = liftIO $ writeIORef (metaRef m) $ Just x

isSolved :: MonadIO m => MetaVar -> m Bool
isSolved = fmap isJust . solution

isUnsolved :: MonadIO m => MetaVar -> m Bool
isUnsolved = fmap isNothing . solution

data WithVar a = WithVar !MetaVar a

instance Eq (WithVar a) where
  WithVar v1 _ == WithVar v2 _ = v1 == v2

instance Pretty a => Pretty (WithVar a) where
  prettyM (WithVar _ x) = prettyM x

prettyMetaVar
  :: (MonadContext e m, MonadLog m, MonadIO m)
  => MetaVar
  -> m Doc
prettyMetaVar x = do
  let name = "?" <> fromNameHint "" fromName (metaHint x) <> shower (metaId x) <> "[" <> shower (metaArity x) <> "]"
  msol <- solution x
  case msol of
    Nothing -> return name
    Just sol -> do
      p <- getLogCategories
      sol' <- prettyMeta $ open sol
      if p "tc.metavar" then
        return $ PP.parens $ name PP.<+> "=" PP.<+> sol'
      else
        return $ PP.parens sol'

prettyMeta
  :: (MonadContext e m, MonadLog m, MonadIO m, HasCallStack)
  => Expr MetaVar Var
  -> m Doc
prettyMeta e = do
  e' <- bitraverse (\m -> WithVar m <$> prettyMetaVar m) prettyVar e
  return $ pretty e'

prettyDefMeta
  :: (MonadContext e m, MonadLog m, MonadIO m)
  => Definition (Expr MetaVar) Var
  -> m Doc
prettyDefMeta e = do
  e' <- bitraverseDefinition (\m -> WithVar m <$> prettyMetaVar m) prettyVar e
  return $ pretty e'

logMeta
  :: (MonadContext e m, MonadLog m, MonadIO m, HasCallStack)
  => Category
  -> String
  -> m (Expr MetaVar Var)
  -> m ()
logMeta c@(Category ct) s me = whenLoggingCategory c $ do
  e <- me
  d <- prettyMeta e
  Effect.log $ "[" <> ct <> "] " <> fromString s <> ": " <> showWide d

logDefMeta
  :: (MonadContext e m, MonadLog m, MonadIO m)
  => Category
  -> String
  -> m (Definition (Expr MetaVar) Var)
  -> m ()
logDefMeta c@(Category ct) s mdef = whenLoggingCategory c $ do
  def <- mdef
  d <- prettyDefMeta def
  Effect.log $ "[" <> ct <> "] " <> fromString s <> ": " <> showWide d

withInstantiatedMetaType
  :: (MonadFresh m, MonadContext (Expr MetaVar Var) m)
  => MetaVar
  -> (Vector Var -> Expr MetaVar Var -> m a)
  -> m a
withInstantiatedMetaType m = withInstantiatedMetaType' (metaArity m) m

withInstantiatedMetaType'
  :: (MonadFresh m, MonadContext (Expr MetaVar Var) m)
  => Int
  -> MetaVar
  -> (Vector Var -> Expr MetaVar Var -> m a)
  -> m a
withInstantiatedMetaType' arity m = go mempty arity (open $ metaType m)
  where
    go vs 0 t k = k (toVector vs) t
    go vs n (Pi h a t s) k =
      Context.freshExtend (binding h a t) $ \v ->
        go (Tsil.Snoc vs v) (n - 1) (instantiate1 (pure v) s) k
    go _ _ _ _ = panic "instantiatedMetaType'"

type MonadBindMetas meta' m = (MonadFresh m, MonadContext (Expr meta' Var) m, MonadLog m, MonadIO m)

-- TODO move?
bindDefMetas
  :: MonadBindMetas meta' m
  => (meta -> Vector (Plicitness, Expr meta Var) -> m (Expr meta' Var))
  -> Definition (Expr meta) Var
  -> m (Definition (Expr meta') Var)
bindDefMetas f def = case def of
  ConstantDefinition a e -> ConstantDefinition a <$> bindMetas f e
  DataDefinition d rep -> DataDefinition <$> bindDataDefMetas f d <*> bindMetas f rep

bindDefMetas'
  :: MonadBindMetas meta' m
  => (meta -> Vector (Plicitness, Expr meta' Var) -> m (Expr meta' Var))
  -> Definition (Expr meta) Var
  -> m (Definition (Expr meta') Var)
bindDefMetas' f = bindDefMetas $ \m es -> do
  es' <- traverse (traverse $ bindMetas' f) es
  f m es'

bindDataDefMetas
  :: MonadBindMetas meta' m
  => (meta -> Vector (Plicitness, Expr meta Var) -> m (Expr meta' Var))
  -> DataDef (Expr meta) Var
  -> m (DataDef (Expr meta') Var)
bindDataDefMetas f (DataDef b ps cs) =
  teleMapExtendContext ps (bindMetas f) $ \vs -> do
    cs' <- forM cs $ \(ConstrDef c s) -> do
      e <- bindMetas f $ instantiateTele pure vs s
      return $ ConstrDef c e
    dataDef b vs cs'

bindMetas
  :: MonadBindMetas meta' m
  => (meta -> Vector (Plicitness, Expr meta Var) -> m (Expr meta' Var))
  -> Expr meta Var
  -> m (Expr meta' Var)
bindMetas f expr = case expr of
  Var v -> return $ Var v
  Meta m es -> f m es
  Global g -> return $ Global g
  Con c -> return $ Con c
  Lit l -> return $ Lit l
  Pi h p t s -> absCase h p t s pi_
  Lam h p t s -> absCase h p t s lam
  App e1 p e2 -> App <$> bindMetas f e1 <*> pure p <*> bindMetas f e2
  Let ds scope ->
    letMapExtendContext ds (bindMetas f) $ \vs -> do
      es <- forMLet ds $ \_ _ s _ -> do
        let e = instantiateLet pure vs s
        bindMetas f e
      let e = instantiateLet pure vs scope
      e' <- bindMetas f e
      let_ (Vector.zip3 vs (letSourceLocs ds) es) e'
  Case e brs t -> Case <$> bindMetas f e <*> bindBranchMetas f brs <*> bindMetas f t
  ExternCode e t -> ExternCode <$> mapM (bindMetas f) e <*> bindMetas f t
  SourceLoc loc e -> SourceLoc loc <$> bindMetas f e
  where
    absCase h p t s c = do
      t' <- bindMetas f t
      Context.freshExtend (binding h p t') $ \v -> do
        let e = instantiate1 (pure v) s
        e' <- bindMetas f e
        c v e'

bindMetas'
  :: MonadBindMetas meta' m
  => (meta -> Vector (Plicitness, Expr meta' Var) -> m (Expr meta' Var))
  -> Expr meta Var
  -> m (Expr meta' Var)
bindMetas' f = bindMetas $ \m es -> do
  es' <- traverse (traverse $ bindMetas' f) es
  f m es'

bindBranchMetas
  :: MonadBindMetas meta' m
  => (meta -> Vector (Plicitness, Expr meta Var) -> m (Expr meta' Var))
  -> Branches (Expr meta) Var
  -> m (Branches (Expr meta') Var)
bindBranchMetas f brs = case brs of
  ConBranches cbrs -> ConBranches <$> do
    forM cbrs $ \(ConBranch c tele scope) ->
      teleMapExtendContext tele (bindMetas f) $ \vs -> do
        let expr = instantiateTele pure vs scope
        expr' <- bindMetas f expr

        conBranch c vs expr'
  LitBranches lbrs def ->
    LitBranches
      <$> mapM (\(LitBranch l br) -> LitBranch l <$> bindMetas f br) lbrs
      <*> bindMetas f def
