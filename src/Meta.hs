{-# LANGUAGE ViewPatterns #-}
module Meta where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.ST.Class
import Data.Foldable
import Data.Function
import Data.Hashable
import Data.Maybe
import Data.Monoid
import qualified Data.Set as S
import Data.STRef
import qualified Data.Traversable as T

import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete as Concrete
import TCM
import Util

type Exists s d a = STRef s (Either Level (AbstractM s d a))

data MetaVar s d a = MetaVar
  { metaId    :: !Int
  , metaType  :: AbstractM s d a
  , metaHint  :: !NameHint
  , metaData  :: !d
  , metaRef   :: !(Maybe (Exists s d a))
  }

type AbstractM s d a = Abstract.Expr a (MetaVar s d a)
type ConcreteM s d a = Concrete.Expr (MetaVar s d a)
type ScopeM b f s d a = Scope b f (MetaVar s d a)
type BranchesM c f s d a = Branches c a f (MetaVar s d a)

instance Eq (MetaVar s d a) where
  (==) = (==) `on` metaId

instance Ord (MetaVar s d a) where
  compare = compare `on` metaId

instance Hashable (MetaVar s d a) where
  hashWithSalt s = hashWithSalt s . metaId

instance (Show d, Show a) => Show (MetaVar s d a) where
  showsPrec d (MetaVar i a h dat _) = showParen (d > 10) $
    showString "Meta" . showChar ' ' . showsPrec 11 i .
    showChar ' ' . showsPrec 11 a . showChar ' ' . showsPrec 11 h .
    showChar ' ' . showsPrec 11 dat .
    showChar ' ' . showString "<Ref>"

showMeta :: (HasRelevance a, HasPlicitness a, Eq a, Functor f, Foldable f, Pretty (f String))
         => f (MetaVar s d a) -> TCM s Doc
showMeta x = do
  vs <- foldMapM S.singleton x
  let p (metaRef -> Just r) = solution r
      p _                   = return $ Left $ Level (-1)
  let vsl = S.toList vs
  pvs <- T.mapM p vsl
  let sv v = "<" ++ (if isJust $ metaRef v then "∃" else "")
          ++ show (metaId v) ++ ":"
          ++ show (pretty $ sv <$> metaType v) ++ ">"
  let solutions = [(sv v, pretty $ fmap sv <$> msol) | (v, msol) <- zip vsl pvs]
  return $ pretty (sv <$> x) <> text ", vars: " <> pretty solutions

tr :: (HasRelevance a, HasPlicitness a, Eq a, Functor f, Foldable f, Pretty (f String))
   => String -> f (MetaVar s d a) -> TCM s ()
tr s x = do
  i <- gets tcIndent
  r <- showMeta x
  TCM.log $ mconcat (replicate i "| ") ++ "--" ++ s ++ ": " ++ showWide r

trp :: Pretty a => String -> a -> TCM s ()
trp s x = do
  i <- gets tcIndent
  TCM.log $ mconcat (replicate i "| ") ++ "--" ++ s ++ ": " ++ showWide (pretty x)

trs :: Show a => String -> a -> TCM s ()
trs s x = do
  i <- gets tcIndent
  TCM.log $ mconcat (replicate i "| ") ++ "--" ++ s ++ ": " ++ show x

existsAtLevel :: NameHint -> AbstractM s d a -> d -> Level -> TCM s (MetaVar s d a)
existsAtLevel hint typ dat l = do
  i   <- fresh
  ref <- liftST $ newSTRef $ Left l
  TCM.log $ "exists: " ++ show i
  return $ MetaVar i typ hint dat (Just ref)

exists :: NameHint -> AbstractM s d a -> d -> TCM s (MetaVar s d a)
exists hint typ dat = existsAtLevel hint typ dat =<< level

existsVar :: Applicative g => NameHint -> AbstractM s d a -> d -> TCM s (g (MetaVar s d a))
existsVar hint typ dat = pure <$> exists hint typ dat

existsVarAtLevel :: Applicative g => NameHint -> AbstractM s d a -> d -> Level -> TCM s (g (MetaVar s d a))
existsVarAtLevel hint typ dat l = pure <$> existsAtLevel hint typ dat l

forall_ :: NameHint -> AbstractM s d a -> d -> TCM s (MetaVar s d a)
forall_ hint typ dat = do
  i <- fresh
  TCM.log $ "forall: " ++ show i
  return $ MetaVar i typ hint dat Nothing

forallVar :: Applicative g => NameHint -> AbstractM s d a -> d -> TCM s (g (MetaVar s d a))
forallVar hint typ dat = pure <$> forall_ hint typ dat

solution :: Exists s d a -> TCM s (Either Level (AbstractM s d a))
solution = liftST . readSTRef

solve :: Exists s d a -> AbstractM s d a -> TCM s ()
solve r x = liftST $ writeSTRef r $ Right x

refineIfSolved :: Exists s d a -> AbstractM s d a -> (AbstractM s d a -> TCM s (AbstractM s d a)) -> TCM s (AbstractM s d a)
refineIfSolved r d f = do
  sol <- solution r
  case sol of
    Left _  -> return d
    Right e -> do
      e' <- f e
      solve r e'
      return e'

letMeta :: NameHint -> AbstractM s d a -> AbstractM s d a -> d -> TCM s (MetaVar s d a)
letMeta hint expr typ dat = do
  i   <- fresh
  ref <- liftST $ newSTRef $ Right expr
  return $ MetaVar i typ hint dat (Just ref)

letVar :: Applicative g
       => NameHint -> AbstractM s d a -> AbstractM s d a -> d -> TCM s (g (MetaVar s d a))
letVar hint expr typ dat = pure <$> letMeta hint expr typ dat

foldMapM :: (Foldable f, Monoid m)
         => (MetaVar s d a -> m) -> f (MetaVar s d a) -> TCM s m
foldMapM f = foldrM go mempty
  where
    go v m = (<> m) . (<> f v) <$> do
      tvs <- foldMapM f $ metaType v
      case metaRef v of
        Just r -> do
          sol <- solution r
          case sol of
            Left _  -> return tvs
            Right c -> foldMapM f c
        Nothing -> return $ f v <> m

abstractM :: (Show d, Show a)
          => (MetaVar s d a -> Maybe b)
          -> AbstractM s d a
          -> TCM s (ScopeM b (Abstract.Expr a) s d a)
abstractM f e = do
  e' <- freeze e
  changed <- liftST $ newSTRef False
  Scope . join <$> traverse (go changed) e'
  where
    -- go :: STRef s Bool -> MetaVar s
    --    -> TCM s (Expr (Var () (Expr (MetaVar s))))
    go changed (f -> Just b) = do
      liftST $ writeSTRef changed True
      return $ pure $ B b
    go changed (v'@(metaRef -> Just r)) = do
      tfvs <- foldMapM S.singleton $ metaType v'
      let mftfvs = S.filter (isJust . f) tfvs
      unless (S.null mftfvs) $ throwError $ "cannot abstract, " ++ show mftfvs ++ " would escape"
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

abstract1M :: (Show d, Show a)
           => MetaVar s d a
           -> AbstractM s d a
           -> TCM s (ScopeM () (Abstract.Expr a) s d a)
abstract1M v e = do
  TCM.log $ "abstracting " ++ show (metaId v)
  abstractM (\v' -> if v == v' then Just () else Nothing) e

etaLamM :: Eq a
        => NameHint
        -> a
        -> Abstract.Expr a (MetaVar s d a)
        -> Scope1 (Abstract.Expr a) (MetaVar s d a)
        -> TCM s (Abstract.Expr a (MetaVar s d a))
etaLamM n p t s = do
  s' <- freezeBound s
  return $ Abstract.etaLam n p t s'

freeze :: AbstractM s d a -> TCM s (AbstractM s d a)
freeze e = join <$> traverse go e
  where
    go v@(metaRef -> Just r) = either (const $ do mt <- freeze (metaType v); return $ pure v {metaType = mt})
                                          freeze =<< solution r
    go v                         = return $ pure v

freezeBound :: (Traversable (t (Abstract.Expr a)), Bound t)
            => t (Abstract.Expr a) (MetaVar s d a)
            -> TCM s (t (Abstract.Expr a) (MetaVar s d a))
freezeBound e = (>>>= id) <$> traverse go e
  where
    go v@(metaRef -> Just r) = either (const $ do mt <- freeze (metaType v); return $ pure v {metaType = mt})
                                          freeze =<< solution r
    go v                         = return $ pure v
