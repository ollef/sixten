{-# LANGUAGE ViewPatterns, OverloadedStrings #-}
module Meta where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.ST.Class
import Data.Foldable
import Data.Function
import Data.Hashable
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Data.STRef
import Data.String
import Data.Vector(Vector)
import Prelude.Extras

import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete.Scoped as Concrete
import qualified Syntax.Sized.SLambda as SLambda
import VIX

type Exists e = STRef (World VIX) (Either Level (e (MetaVar e)))

data MetaVar e = MetaVar
  { metaId   :: !Int
  , metaType :: e (MetaVar e)
  , metaHint :: !NameHint
  , metaRef  :: !(Maybe (Exists e))
  }

type MetaA = MetaVar Abstract.Expr

type ConcreteM = Concrete.Expr MetaA
type AbstractM = Abstract.Expr MetaA
type LambdaM = SLambda.Expr MetaA
type ScopeM b f = Scope b f MetaA
type BranchesM c a f = Branches c a f MetaA

instance Eq (MetaVar e) where
  (==) = (==) `on` metaId

instance Ord (MetaVar e) where
  compare = compare `on` metaId

instance Hashable (MetaVar e) where
  hashWithSalt s = hashWithSalt s . metaId

instance Show1 e => Show (MetaVar e) where
  showsPrec d (MetaVar i t h _) = showParen (d > 10) $
    showString "MetaA" . showChar ' ' . showsPrec 11 i .
    showChar ' ' . showsPrec1 11 t . showChar ' ' . showsPrec 11 h .
    showChar ' ' . showString "<Ref>"

forall :: NameHint -> e (MetaVar e) -> VIX (MetaVar e)
forall hint typ = do
  i <- fresh
  logVerbose 20 $ "forall: " <> fromString (show i)
  return $ MetaVar i typ hint Nothing

refineVar
  :: Applicative e
  => MetaVar e
  -> (e (MetaVar e) -> VIX (e (MetaVar e)))
  -> VIX (e (MetaVar e))
refineVar v@(metaRef -> Nothing) _ = return $ pure v
refineVar v@(metaRef -> Just r) f = refineIfSolved r (pure v) f
refineVar _ _ = error "refineVar impossible"

showMeta
  :: (Functor e, Foldable e, Functor f, Foldable f, Pretty (f String), Pretty (e String))
  => f (MetaVar e)
  -> VIX Doc
showMeta x = do
  vs <- foldMapM Set.singleton x
  let p (metaRef -> Just r) = solution r
      p _                   = return $ Left $ Level (-1)
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
  :: (Functor e, Foldable e, Functor f, Foldable f, Pretty (f String), Pretty (e String))
  => Int
  -> String
  -> f (MetaVar e)
  -> VIX ()
logMeta v s x = whenVerbose v $ do
  i <- gets vixIndent
  r <- showMeta x
  VIX.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide r

existsAtLevel :: NameHint -> e (MetaVar e) -> Level -> VIX (MetaVar e)
existsAtLevel hint typ l = do
  i   <- fresh
  ref <- liftST $ newSTRef $ Left l
  logVerbose 20 $ "exists: " <> fromString (show i)
  return $ MetaVar i typ hint (Just ref)

exists :: NameHint -> e (MetaVar e) -> VIX (MetaVar e)
exists hint typ = existsAtLevel hint typ =<< level

existsVar
  :: Applicative g
  => NameHint
  -> e (MetaVar e)
  -> VIX (g (MetaVar e))
existsVar hint typ = pure <$> exists hint typ

solution :: Exists e -> VIX (Either Level (e (MetaVar e)))
solution = liftST . readSTRef

solve :: Exists e -> e (MetaVar e) -> VIX ()
solve r x = liftST $ writeSTRef r $ Right x

refineIfSolved
  :: Exists e
  -> e (MetaVar e)
  -> (e (MetaVar e) -> VIX (e (MetaVar e)))
  -> VIX (e (MetaVar e))
refineIfSolved r d f = do
  sol <- solution r
  case sol of
    Left _  -> return d
    Right e -> do
      e' <- f e
      solve r e'
      return e'

foldMapM
  :: (Foldable e, Foldable f, Monoid m)
  => (MetaVar e -> m)
  -> f (MetaVar e)
  -> VIX m
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
  :: (Monad e, Traversable e, Show1 e)
  => (MetaVar e -> Maybe b)
  -> e (MetaVar e)
  -> VIX (Scope b e (MetaVar e))
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
    go changed (v'@(metaRef -> Just r)) = do
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

abstract1M
  :: MetaA
  -> AbstractM
  -> VIX (ScopeM () Abstract.Expr)
abstract1M v e = do
  logVerbose 20 $ "abstracting " <> fromString (show $ metaId v)
  abstractM (\v' -> if v == v' then Just () else Nothing) e

zonkVar
  :: (Monad e, Traversable e)
  => MetaVar e
  -> VIX (e (MetaVar e))
zonkVar v@(metaRef -> Just r) = do
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
  :: (Monad e, Traversable e)
  => e (MetaVar e)
  -> VIX (e (MetaVar e))
zonk = fmap join . traverse zonkVar

zonkBound
  :: (Monad e, Traversable e, Traversable (t e), Bound t)
  => t e (MetaVar e)
  -> VIX (t e (MetaVar e))
zonkBound = fmap (>>>= id) . traverse zonkVar

metaTelescope
  :: Monad e
  => Vector (a, MetaVar e)
  -> Telescope a e (MetaVar e)
metaTelescope vs =
  Telescope
  $ (\(a, v) -> (metaHint v, a, abstract abstr $ metaType v))
  <$> vs
  where
    abstr = teleAbstraction $ snd <$> vs

metaTelescopeM
  :: (Monad e, Traversable e, Show1 e)
  => Vector (a, MetaVar e)
  -> VIX (Telescope a e (MetaVar e))
metaTelescopeM vs =
  fmap Telescope $ forM vs $ \(a, v) -> do
    s <- abstractM abstr $ metaType v
    return (metaHint v, a, s)
  where
    abstr = teleAbstraction $ snd <$> vs
