{-# LANGUAGE ViewPatterns #-}
module Meta where

import Bound
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

import Annotation
import Branches
import Hint
import qualified Core
import qualified Input
import Monad
import Pretty

type Exists s d a = STRef s (Either Level (CoreM s d a))

data MetaVar s d a = MetaVar
  { metaId    :: {-# UNPACK #-} !Int
  , metaType  :: CoreM s d a
  , metaHint  :: {-# UNPACK #-} !NameHint
  , metaData  :: !d
  , metaRef   :: {-# UNPACK #-} !(Maybe (Exists s d a))
  }

type CoreM s d a = Core.Expr a (MetaVar s d a)
type InputM s d a = Input.Expr (MetaVar s d a)
type ScopeM b f s d a = Scope b (f a) (MetaVar s d a)
type InputBranchesM s d a = Branches Input.Expr (MetaVar s d a)
type CoreBranchesM s d a = Branches (Core.Expr a) (MetaVar s d a)

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
  Monad.log $ mconcat (replicate i "| ") ++ "--" ++ s ++ ": " ++ showWide r

trp :: Pretty a => String -> a -> TCM s ()
trp s x = do
  i <- gets tcIndent
  Monad.log $ mconcat (replicate i "| ") ++ "--" ++ s ++ ": " ++ showWide (pretty x)

trs :: Show a => String -> a -> TCM s ()
trs s x = do
  i <- gets tcIndent
  Monad.log $ mconcat (replicate i "| ") ++ "--" ++ s ++ ": " ++ show x

existsAtLevel :: NameHint -> CoreM s d a -> d -> Level -> TCM s (MetaVar s d a)
existsAtLevel hint typ dat l = do
  i   <- fresh
  ref <- liftST $ newSTRef $ Left l
  Monad.log $ "exists: " ++ show i
  return $ MetaVar i typ hint dat (Just ref)

exists :: NameHint -> CoreM s d a -> d -> TCM s (MetaVar s d a)
exists hint typ dat = existsAtLevel hint typ dat =<< level

existsVar :: Applicative g => NameHint -> CoreM s d a -> d -> TCM s (g (MetaVar s d a))
existsVar hint typ dat = pure <$> exists hint typ dat

existsVarAtLevel :: Applicative g => NameHint -> CoreM s d a -> d -> Level -> TCM s (g (MetaVar s d a))
existsVarAtLevel hint typ dat l = pure <$> existsAtLevel hint typ dat l

forall_ :: NameHint -> CoreM s d a -> d -> TCM s (MetaVar s d a)
forall_ hint typ dat = do
  i <- fresh
  Monad.log $ "forall: " ++ show i
  return $ MetaVar i typ hint dat Nothing

forallVar :: Applicative g => NameHint -> CoreM s d a -> d -> TCM s (g (MetaVar s d a))
forallVar hint typ dat = pure <$> forall_ hint typ dat

solution :: Exists s d a -> TCM s (Either Level (CoreM s d a))
solution = liftST . readSTRef

solve :: Exists s d a -> CoreM s d a -> TCM s ()
solve r x = liftST $ writeSTRef r $ Right x

refineIfSolved :: Exists s d a -> CoreM s d a -> (CoreM s d a -> TCM s (CoreM s d a)) -> TCM s (CoreM s d a)
refineIfSolved r d f = do
  sol <- solution r
  case sol of
    Left _  -> return d
    Right e -> do
      e' <- f e
      solve r e'
      return e'

letMeta :: NameHint -> CoreM s d a -> CoreM s d a -> d -> TCM s (MetaVar s d a)
letMeta hint expr typ dat = do
  i   <- fresh
  ref <- liftST $ newSTRef $ Right expr
  return $ MetaVar i typ hint dat (Just ref)

letVar :: Applicative g
       => NameHint -> CoreM s d a -> CoreM s d a -> d -> TCM s (g (MetaVar s d a))
letVar hint expr typ dat = pure <$> letMeta hint expr typ dat

foldMapM :: (Foldable f, Monoid m)
         => (MetaVar s d a -> m) -> f (MetaVar s d a) -> TCM s m
foldMapM f = foldrM go mempty
  where
    go v m = (<> m) . (<> f v) <$> do
      tvs <- foldMapM f $ metaType v
      (<> tvs) <$> case metaRef v of
        Just r -> do
          sol <- solution r
          case sol of
            Left _  -> return mempty
            Right c -> foldMapM f c
        Nothing -> return $ f v <> m

abstractM :: (Show d, Show a)
          => (MetaVar s d a -> Maybe b)
          -> CoreM s d a
          -> TCM s (ScopeM b Core.Expr s d a)
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
           -> CoreM s d a
           -> TCM s (ScopeM () Core.Expr s d a)
abstract1M v e = do
  Monad.log $ "abstracting " ++ show (metaId v)
  abstractM (\v' -> if v == v' then Just () else Nothing) e

freeze :: CoreM s d a -> TCM s (CoreM s d a)
freeze e = join <$> traverse go e
  where
    go v@(metaRef -> Just r) = either (const $ do mt <- freeze (metaType v); return $ pure v {metaType = mt})
                                          freeze =<< solution r
    go v                         = return $ pure v
