{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, ViewPatterns, OverloadedStrings #-}
module Inference.Meta where

import Control.Monad.Except
import Control.Monad.ST
import Control.Monad.State
import Data.Foldable
import Data.Function
import Data.Functor.Classes
import Data.Hashable
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.Maybe
import Data.Monoid
import Data.STRef
import Data.String
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector(Vector)

import Fresh
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete.Scoped as Concrete
import qualified Syntax.Sized.SLambda as SLambda
import Util
import VIX

newtype Level = Level Int
  deriving (Eq, Num, Ord, Show)

instance Pretty Level where
  pretty (Level i) = pretty i

type Exists d e = STRef RealWorld (Either Level (e (MetaVar d e)))

data MetaRef d e
  = Forall
  | Exists (Exists d e)
  | LetRef (STRef RealWorld (e (MetaVar d e)))

data MetaVar d e = MetaVar
  { metaId  :: !Int
  , metaType :: e (MetaVar d e)
  , metaHint :: !NameHint
  , metaRef :: !(MetaRef d e)
  , metaData :: !d
  }

type MetaA = MetaVar Plicitness Abstract.Expr

type ConcreteM = Concrete.Expr MetaA
type AbstractM = Abstract.Expr MetaA
type LambdaM = SLambda.Expr MetaA
type ScopeM b f = Scope b f MetaA

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
refineVar v@MetaVar { metaRef = Forall } _ = return $ pure v
refineVar v@MetaVar { metaRef = Exists r } f = do
  sol <- solution r
  case sol of
    Left _  -> return $ pure v
    Right e -> do
      e' <- f e
      solve r e'
      return e'
refineVar MetaVar { metaRef = LetRef r } f = do
  e <- liftST $ readSTRef r
  e' <- f e
  liftST $ writeSTRef r e'
  return e'

forall
  :: (MonadVIX m, MonadIO m)
  => NameHint
  -> d
  -> e (MetaVar d e)
  -> m (MetaVar d e)
forall hint d typ = do
  i <- fresh
  logVerbose 20 $ "forall: " <> fromString (show i)
  return $ MetaVar i typ hint Forall d

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
  return $ MetaVar i typ hint (Exists ref) d

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
  logVerbose 20 $ "shared: " <> fromString (show i)
  return $ MetaVar i typ hint (Exists ref) d

let_
  :: (MonadVIX m, MonadIO m)
  => NameHint
  -> d
  -> e (MetaVar d e)
  -> e (MetaVar d e)
  -> m (MetaVar d e)
let_ hint d expr typ = do
  i <- fresh
  ref <- liftST $ newSTRef expr
  logVerbose 20 $ "let: " <> fromString (show i)
  return $ MetaVar i typ hint (LetRef ref) d

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

foldMapMetas
  :: (Foldable e, Foldable f, Monoid a, MonadIO m)
  => (MetaVar d e -> a)
  -> f (MetaVar d e)
  -> m a
foldMapMetas f = flip evalStateT mempty . foldrM go mempty
  where
    go v m = do
      visited <- gets $ HashMap.lookup v
      case visited of
        Just a -> return $ a <> m
        Nothing -> do
          modify $ HashMap.insert v mempty
          result <- case metaRef v of
            Exists ref -> do
              sol <- lift $ solution ref
              case sol of
                Left _ -> return $ f v <> m
                Right c -> do
                  r <- foldrM go mempty c
                  return $ f v <> r <> m
            Forall -> return $ f v <> m
            LetRef _ -> return $ f v <> m
          modify $ HashMap.insert v result
          return result

abstractM
  :: (Monad e, Traversable e, Show1 e, MonadVIX m, MonadIO m, MonadError Error m)
  => (MetaVar d e -> Maybe b)
  -> e (MetaVar d e)
  -> m (Scope b e (MetaVar d e))
abstractM f e = do
  changed <- liftST $ newSTRef False
  Scope . join <$> traverse (go changed) e
  where
    go changed (f -> Just b) = do
      liftST $ writeSTRef changed True
      return $ pure $ B b
    go changed v'@MetaVar { metaRef = Exists r } = do
      sol <- solution r
      case sol of
        Left _ -> do
          tfvs <- foldMapMetas HashSet.singleton $ metaType v'
          let mftfvs = HashSet.filter (isJust . f) tfvs
          unless (HashSet.null mftfvs)
            $ throwLocated $ "Cannot abstract," PP.<+> shower mftfvs PP.<+> "would escape from the type of"
            PP.<+> shower v'
          free v'
        Right c -> do
          changed' <- liftST $ newSTRef False
          c' <- traverse (go changed') c
          hasChanged <- liftST $ readSTRef changed'
          if hasChanged then do
            liftST $ writeSTRef changed True
            return $ join c'
          else
            free v'
    go _ v'@MetaVar { metaRef = Forall } = free v'
    go _ v'@MetaVar { metaRef = LetRef _ } = free v'
    free = pure . pure . pure . pure

bindM
  :: (Monad e, Traversable e, MonadIO m)
  => (MetaVar d e -> m (e (MetaVar d e)))
  -> e (MetaVar d e)
  -> m (e (MetaVar d e))
bindM f = fmap join . traverse go
  where
    go v@MetaVar { metaRef = Exists r } = do
      sol <- solution r
      case sol of
        Left _ -> do
          typ' <- bindM f $ metaType v
          f v { metaType = typ' }
        Right x -> bindM f x
    go v = f v

boundM
  :: (GlobalBound b, GlobalBind e, Traversable e, Traversable (b e), MonadIO m)
  => (MetaVar d e -> m (e (MetaVar d e)))
  -> b e (MetaVar d e)
  -> m (b e (MetaVar d e))
boundM f = fmap boundJoin . traverse go
  where
    go v@MetaVar { metaRef = Exists r } = do
      sol <- solution r
      case sol of
        Left _ -> do
          typ' <- bindM f $ metaType v
          f v { metaType = typ' }
        Right x -> bindM f x
    go v = f v

abstract1M
  :: (MonadIO m, MonadVIX m, MonadError Error m)
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
zonkVar v@MetaVar { metaRef = Exists r } = do
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

semiZonk
  :: MonadIO m
  => AbstractM
  -> m AbstractM
semiZonk e@(Abstract.Var MetaVar { metaRef = Exists r }) = do
  sol <- solution r
  case sol of
    Left _ -> return e
    Right e' -> do
      e'' <- semiZonk e'
      solve r e''
      return e''
semiZonk e = return e

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
  :: (Monad e, Traversable e, Show1 e, MonadVIX m, MonadIO m, MonadError Error m)
  => Vector (a, MetaVar d e)
  -> m (Telescope a e (MetaVar d e))
metaTelescopeM vs =
  fmap Telescope $ forM vs $ \(a, v) -> do
    s <- abstractM abstr $ metaType v
    return $ TeleArg (metaHint v) a s
  where
    abstr = teleAbstraction $ snd <$> vs

showMeta
  :: (Functor e, Foldable e, Functor f, Foldable f, Pretty (f Doc), Pretty (e Doc), MonadIO m)
  => f (MetaVar d e)
  -> m Doc
showMeta x = do
  vs <- foldMapMetas HashSet.singleton x
  let p MetaVar { metaRef = Exists r } = solution r
      p _ = return $ Left $ Level (-1)
  let vsl = HashSet.toList vs
  pvs <- mapM p vsl
  let showVar :: MetaVar d e -> Doc
      showVar v
        = "$" <> fromNameHint "" fromName (metaHint v) <> refType (metaRef v)
       <> shower (metaId v)
  let solutions = [(showVar v, pretty $ showVar <$> metaType v, pretty $ fmap showVar <$> msol) | (v, msol) <- zip vsl pvs]
  return
    $ pretty (showVar <$> x)
    <> if null solutions
      then mempty
      else ", metavars: " <> pretty solutions
  where
    refType (Exists _) = "∃"
    refType Forall = ""
    refType LetRef {} = ""

logMeta
  :: (Functor e, Foldable e, Functor f, Foldable f, Pretty (f Doc), Pretty (e Doc), MonadIO m, MonadVIX m)
  => Int
  -> String
  -> f (MetaVar d e)
  -> m ()
logMeta v s x = whenVerbose v $ do
  i <- liftVIX $ gets vixIndent
  r <- showMeta x
  VIX.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide r
