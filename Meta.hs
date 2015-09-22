{-# LANGUAGE ViewPatterns #-}
module Meta where

import Bound
import Bound.Var
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
import Hint
import qualified Core
import qualified Input
import Monad
import Pretty
import Util

type Exists s v = STRef s (Either Level (Core s v))

data MetaVar s v = MetaVar
  { metaId    :: {-# UNPACK #-} !Int
  , metaType  :: Core s v
  , metaHint  :: {-# UNPACK #-} !NameHint
  , metaRef   :: {-# UNPACK #-} !(Maybe (Exists s v))
  }

instance Eq (MetaVar s v) where
  (==) = (==) `on` metaId

instance Ord (MetaVar s v) where
  compare = compare `on` metaId

instance Hashable (MetaVar s v) where
  hashWithSalt s = hashWithSalt s . metaId

instance Show v => Show (MetaVar s v) where
  showsPrec d (MetaVar i a h _) = showParen (d > 10) $
    showString "Meta" . showChar ' ' . showsPrec 11 i .
    showChar ' ' . showsPrec 11 a . showChar ' ' . showsPrec 11 h .
    showChar ' ' . showString "<Ref>"

type Input      s   v = Input.Expr (Var v (MetaVar s v))
type InputScope s b v = Scope b Input.Expr (Var v (MetaVar s v))
type Core       s   v = Core.Expr Plicitness (Var v (MetaVar s v))
type CoreScope  s b v = Scope b (Core.Expr Plicitness) (Var v (MetaVar s v))

showMeta :: (Functor f, Foldable f, Show v, Pretty (f String)) => f (Var v (MetaVar s v)) -> TCM s v' Doc
showMeta x = do
  vs <- foldMapM S.singleton x
  let p (metaRef -> Just r) = solution r
      p _                   = return $ Left $ Level (-1)
  let vsl = S.toList vs
  pvs <- T.mapM p vsl
  let sv v = "<" ++ (if isJust $ metaRef v then "∃" else "") ++ show (metaId v) ++ ":" ++ show (pretty $ unvar show sv <$> metaType v) ++ ">"
  let solutions = [(sv v, pretty $ fmap (unvar show sv) <$> msol) | (v, msol) <- zip vsl pvs]
  return $ pretty (unvar show sv <$> x) <> text ", vars: " <> pretty solutions

tr :: (Functor f, Foldable f, Pretty (f String), Show v) => String -> f (Var v (MetaVar s v)) -> TCM s v' ()
tr s x = do
  i <- gets tcIndent
  r <- showMeta x
  Monad.log $ mconcat (replicate i "| ") ++ "--" ++ s ++ ": " ++ showWide r

freshExistsL :: NameHint -> Core s v -> Level -> TCM s v' (MetaVar s v)
freshExistsL h a l = do
  i   <- fresh
  ref <- liftST $ newSTRef $ Left l
  Monad.log $ "exists: " ++ show i
  return $ MetaVar i a h (Just ref)

freshExists :: NameHint -> Core s v -> TCM s v' (MetaVar s v)
freshExists h a = freshExistsL h a =<< level

freshExistsV :: Monad g => NameHint -> Core s v -> TCM s v' (g (Var v (MetaVar s v)))
freshExistsV h a = return . F <$> freshExists h a

freshExistsLV :: Monad g => NameHint -> Core s v -> Level -> TCM s v' (g (Var v (MetaVar s v)))
freshExistsLV h a l = return . F <$> freshExistsL h a l

freshForall :: NameHint -> Core s v -> TCM s v' (MetaVar s v)
freshForall h a = do
  i <- fresh
  Monad.log $ "forall: " ++ show i
  return $ MetaVar i a h Nothing

freshForallV :: Monad g => NameHint -> Core s v -> TCM s v' (g (Var v (MetaVar s v)))
freshForallV h a = return . F <$> freshForall h a

solution :: Exists s v -> TCM s v' (Either Level (Core s v))
solution = liftST . readSTRef

solve :: Exists s v -> Core s v -> TCM s v' ()
solve r x = liftST $ writeSTRef r $ Right x

refineIfSolved :: Exists s v -> Core s v -> (Core s v -> TCM s v' (Core s v)) -> TCM s v' (Core s v)
refineIfSolved r d f = do
  sol <- solution r
  case sol of
    Left _  -> return d
    Right e -> do
      e' <- f e
      solve r e'
      return e'

freshLet :: NameHint -> Core s v -> Core s v -> TCM s v' (MetaVar s v)
freshLet h e t = do
  i   <- fresh
  ref <- liftST $ newSTRef $ Right e
  return $ MetaVar i t h (Just ref)

freshLetV :: Monad g => NameHint -> Core s v -> Core s v -> TCM s v' (g (Var v (MetaVar s v)))
freshLetV h e t = (return . F) <$> freshLet h e t

foldMapM :: (Foldable f, Monoid m) => (MetaVar s v -> m) -> f (Var v (MetaVar s v)) -> TCM s v' m
foldMapM f = foldrM go mempty
  where
    go (B _) m = return m
    go (F v) m = (<> m) . (<> f v) <$> do
      tvs <- foldMapM f $ metaType v
      (<> tvs) <$> case metaRef v of
        Just r -> do
          sol <- solution r
          case sol of
            Left _  -> return mempty
            Right c -> foldMapM f c
        Nothing -> return $ f v <> m

abstractM :: Show v
          => (MetaVar s v -> Maybe b)
          -> Core s v
          -> TCM s v' (Scope b (Core.Expr Plicitness) (Var v (MetaVar s v)))
abstractM f e = do
  e' <- freeze e
  changed <- liftST $ newSTRef False
  (Scope . join) <$> traverse (go changed) e'
  where
    -- go :: STRef s Bool -> Var Name (MetaVar s)
    --    -> TCM s (Expr (Var () (Expr (Var Name (MetaVar s)))))
    go changed (F (f -> Just b)) = do
      liftST $ writeSTRef changed True
      return $ return $ B b
    go changed (F v'@(metaRef -> Just r)) = do
      tfvs <- foldMapM S.singleton $ metaType v'
      let mftfvs = S.filter (isJust . f) tfvs
      unless (S.null mftfvs) $ throwError $ "cannot abstract, " ++ show mftfvs ++ " would escape"
      sol <- solution r
      case sol of
        Left _  -> free $ F v'
        Right c -> do
          changed' <- liftST $ newSTRef False
          c' <- traverse (go changed') c
          hasChanged <- liftST $ readSTRef changed'
          if hasChanged then do
            liftST $ writeSTRef changed True
            return $ join c'
          else
            free $ F v'
    go _ v' = free v'
    free = return . return . return . return

abstract1M :: Show v
           => MetaVar s v
           -> Core s v
           -> TCM s v' (Scope1 (Core.Expr Plicitness) (Var v (MetaVar s v)))
abstract1M v e = do
  Monad.log $ "abstracting " ++ show (metaId v)
  abstractM (\v' -> if v == v' then Just () else Nothing) e

freeze :: Core s v -> TCM s v' (Core s v)
freeze e = join <$> traverse go e
  where
    go (F v@(metaRef -> Just r)) = either (const $ do mt <- freeze (metaType v); return $ return $ F v {metaType = mt})
                                          freeze =<< solution r
    go v                         = return $ return v
