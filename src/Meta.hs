{-# LANGUAGE FlexibleContexts, ViewPatterns, OverloadedStrings #-}
module Meta where

import Control.Monad.Except
import Control.Monad.ST
import Control.Monad.State
import Data.Foldable
import Data.Function
import Data.Functor.Classes
import Data.Hashable
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Data.STRef
import Data.String
import Data.Vector(Vector)

import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete.Scoped as Concrete
import qualified Syntax.Sized.SLambda as SLambda
import VIX

type Exists d e = STRef RealWorld (Either Level (e (MetaVar d e)))

data MetaVar d e = MetaVar
  { metaId  :: !Int
  , metaType :: e (MetaVar d e)
  , metaHint :: !NameHint
  , metaRef :: !(Maybe (Exists d e))
  , metaData :: !d
  }

type MetaA = MetaVar Plicitness Abstract.Expr

type ConcreteM = Concrete.Expr MetaA
type AbstractM = Abstract.Expr MetaA
type LambdaM = SLambda.Expr MetaA
type ScopeM b f = Scope b f MetaA
type BranchesM c a f = Branches c a f MetaA

instance Eq (MetaVar d e) where
  (==) = (==) `on` metaId

instance Ord (MetaVar d e) where
  compare = compare `on` metaId

instance Hashable (MetaVar d e) where
  hashWithSalt s = hashWithSalt s . metaId

instance Show1 e => Show (MetaVar d e) where
  showsPrec d (MetaVar i t h _ _) = showParen (d > 10) $
    showString "Meta" . showChar ' ' . showsPrec 11 i .
    showChar ' ' . showsPrec1 11 t . showChar ' ' . showsPrec 11 h .
    showChar ' ' . showString "<Ref>"

refineVar
  :: (Applicative e, MonadIO m)
  => MetaVar d e
  -> (e (MetaVar d e) -> m (e (MetaVar d e)))
  -> m (e (MetaVar d e))
refineVar v@MetaVar { metaRef = Nothing } _ = return $ pure v
refineVar v@MetaVar { metaRef = Just r } f = refineIfSolved r (pure v) f

forall
  :: (MonadVIX m, MonadIO m)
  => NameHint
  -> d
  -> e (MetaVar d e)
  -> m (MetaVar d e)
forall hint d typ = do
  i <- fresh
  logVerbose 20 $ "forall: " <> fromString (show i)
  return $ MetaVar i typ hint Nothing d

existsAtLevel
  :: (MonadVIX m, MonadIO m)
  => NameHint
  -> d
  -> e (MetaVar d e)
  -> Level
  -> m (MetaVar d e)
existsAtLevel hint d typ l = do
  i <- fresh
  ref <- liftST $ newSTRef $ Left l
  logVerbose 20 $ "exists: " <> fromString (show i)
  return $ MetaVar i typ hint (Just ref) d

exists
  :: (MonadVIX m, MonadIO m)
  => NameHint
  -> d
  -> e (MetaVar d e)
  -> m (MetaVar d e)
exists hint d typ = existsAtLevel hint d typ =<< level

shared
  :: (MonadVIX m, MonadIO m)
  => NameHint
  -> d
  -> e (MetaVar d e)
  -> e (MetaVar d e)
  -> m (MetaVar d e)
shared hint d expr typ = do
  i <- fresh
  ref <- liftST $ newSTRef $ Right expr
  logVerbose 20 $ "let: " <> fromString (show i)
  return $ MetaVar i typ hint (Just ref) d

solution
  :: MonadIO m
  => Exists d e
  -> m (Either Level (e (MetaVar d e)))
solution = liftST . readSTRef

solve
  :: MonadIO m
  => Exists d e
  -> e (MetaVar d e)
  -> m ()
solve r x = liftST $ writeSTRef r $ Right x

refineIfSolved
  :: MonadIO m
  => Exists d e
  -> e (MetaVar d e)
  -> (e (MetaVar d e) -> m (e (MetaVar d e)))
  -> m (e (MetaVar d e))
refineIfSolved r d f = do
  sol <- solution r
  case sol of
    Left _  -> return d
    Right e -> do
      e' <- f e
      solve r e'
      return e'

foldMapM
  :: (Foldable e, Foldable f, Monoid a, MonadIO m)
  => (MetaVar d e -> a)
  -> f (MetaVar d e)
  -> m a
foldMapM f = foldrM go mempty
  where
    go v m = (<> m) . (<> f v) <$>
      case metaRef v of
        Just r -> do
          sol <- solution r
          case sol of
            Left _  -> foldMapM f $ metaType v
            Right c -> foldMapM f c
        Nothing -> return mempty

abstractM
  :: (Monad e, Traversable e, Show1 e, MonadError String m, MonadIO m)
  => (MetaVar d e -> Maybe b)
  -> e (MetaVar d e)
  -> m (Scope b e (MetaVar d e))
abstractM f e = do
  e' <- zonk e
  changed <- liftST $ newSTRef False
  Scope . join <$> traverse (go changed) e'
  where
    -- go :: STRef s Bool -> MetaVar s
    --    -> VIX (Expr (Var () (Expr (MetaVar s))))
    go changed (f -> Just b) = do
      liftST $ writeSTRef changed True
      return $ pure $ B b
    go changed v'@MetaVar { metaRef = Just r } = do
      tfvs <- foldMapM Set.singleton $ metaType v'
      let mftfvs = Set.filter (isJust . f) tfvs
      unless (Set.null mftfvs)
        $ throwError $ "cannot abstract, " ++ show mftfvs ++ " would escape from the type of "
        ++ show v'
      sol <- solution r
      case sol of
        Left _  -> free v'
        Right c -> do
          changed' <- liftST $ newSTRef False
          c' <- traverse (go changed') c
          hasChanged <- liftST $ readSTRef changed'
          if hasChanged then do
            liftST $ writeSTRef changed True
            return $ join c'
          else
            free v'
    go _ v' = free v'
    free = pure . pure . pure . pure

bindM
  :: (Monad e, Traversable e, MonadIO m)
  => (MetaVar d e -> m (e v))
  -> e (MetaVar d e)
  -> m (e v)
bindM f = fmap join . traverse go
  where
    go v@MetaVar { metaRef = Just r } = do
      sol <- solution r
      case sol of
        Left _ -> f v
        Right x -> bindM f x
    go v = f v

abstract1M
  :: (MonadIO m, MonadVIX m, MonadError String m)
  => MetaA
  -> AbstractM
  -> m (ScopeM () Abstract.Expr)
abstract1M v e = do
  logVerbose 20 $ "abstracting " <> fromString (show $ metaId v)
  abstractM (\v' -> if v == v' then Just () else Nothing) e

zonkVar
  :: (Monad e, Traversable e, MonadIO m)
  => MetaVar d e
  -> m (e (MetaVar d e))
zonkVar v@MetaVar { metaRef = Just r } = do
  sol <- solution r
  case sol of
    Left _ -> do
      mt <- zonk $ metaType v
      return $ pure v {metaType = mt}
    Right e -> do
      e' <- zonk e
      solve r e'
      return e'
zonkVar v = return $ pure v

zonk
  :: (Monad e, Traversable e, MonadIO m)
  => e (MetaVar d e)
  -> m (e (MetaVar d e))
zonk = fmap join . traverse zonkVar

zonkBound
  :: (Monad e, Traversable e, Traversable (t e), Bound t, MonadIO m)
  => t e (MetaVar d e)
  -> m (t e (MetaVar d e))
zonkBound = fmap (>>>= id) . traverse zonkVar

metaTelescope
  :: Monad e
  => Vector (a, MetaVar d e)
  -> Telescope a e (MetaVar d e)
metaTelescope vs =
  Telescope
  $ (\(a, v) -> TeleArg (metaHint v) a $ abstract abstr $ metaType v)
  <$> vs
  where
    abstr = teleAbstraction $ snd <$> vs

metaTelescopeM
  :: (Monad e, Traversable e, Show1 e, MonadIO m, MonadError String m)
  => Vector (a, MetaVar d e)
  -> m (Telescope a e (MetaVar d e))
metaTelescopeM vs =
  fmap Telescope $ forM vs $ \(a, v) -> do
    s <- abstractM abstr $ metaType v
    return $ TeleArg (metaHint v) a s
  where
    abstr = teleAbstraction $ snd <$> vs

showMeta
  :: (Functor e, Foldable e, Functor f, Foldable f, Pretty (f String), Pretty (e String), MonadIO m)
  => f (MetaVar d e)
  -> m Doc
showMeta x = do
  vs <- foldMapM Set.singleton x
  let p MetaVar { metaRef = Just r } = solution r
      p _ = return $ Left $ Level (-1)
  let vsl = Set.toList vs
  pvs <- mapM p vsl
  let sv v = "$" ++ fromMaybe "" (fromName <$> unNameHint (metaHint v)) ++ (if isJust $ metaRef v then "∃" else "")
          ++ show (metaId v)
  let solutions = [(sv v, pretty $ sv <$> metaType v, pretty $ fmap sv <$> msol) | (v, msol) <- zip vsl pvs]
  return
    $ pretty (sv <$> x)
    <> if null solutions
      then mempty
      else text ", metavars: " <> pretty solutions

logMeta
  :: (Functor e, Foldable e, Functor f, Foldable f, Pretty (f String), Pretty (e String), MonadIO m, MonadVIX m)
  => Int
  -> String
  -> f (MetaVar d e)
  -> m ()
logMeta v s x = whenVerbose v $ do
  i <- gets vixIndent
  r <- showMeta x
  VIX.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide r
