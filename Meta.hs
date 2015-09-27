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

type Exists s d a v = STRef s (Either Level (CoreM s d a v))

data MetaVar s d a v = MetaVar
  { metaId    :: {-# UNPACK #-} !Int
  , metaType  :: CoreM s d a v
  , metaHint  :: {-# UNPACK #-} !NameHint
  , metaData  :: !d
  , metaRef   :: {-# UNPACK #-} !(Maybe (Exists s d a v))
  }

type CoreM s d a v = Core.Expr a (Var v (MetaVar s d a v))
type InputM s d a v = Input.Expr (Var v (MetaVar s d a v))
type ScopeM b f s d a v = Scope b (f a) (Var v (MetaVar s d a v))

instance Eq (MetaVar s d a v) where
  (==) = (==) `on` metaId

instance Ord (MetaVar s d a v) where
  compare = compare `on` metaId

instance Hashable (MetaVar s d a v) where
  hashWithSalt s = hashWithSalt s . metaId

instance (Show d, Show a, Show v) => Show (MetaVar s d a v) where
  showsPrec d (MetaVar i a h dat _) = showParen (d > 10) $
    showString "Meta" . showChar ' ' . showsPrec 11 i .
    showChar ' ' . showsPrec 11 a . showChar ' ' . showsPrec 11 h .
    showChar ' ' . showsPrec 11 dat .
    showChar ' ' . showString "<Ref>"

showMeta :: (HasRelevance a, HasPlicitness a, Eq a, Functor f, Foldable f, Show v, Pretty (f String))
         => f (Var v (MetaVar s d a v)) -> TCM s v' Doc
showMeta x = do
  vs <- foldMapM S.singleton x
  let p (metaRef -> Just r) = solution r
      p _                   = return $ Left $ Level (-1)
  let vsl = S.toList vs
  pvs <- T.mapM p vsl
  let sv v = "<" ++ (if isJust $ metaRef v then "∃" else "") ++ show (metaId v) ++ ":" ++ show (pretty $ unvar show sv <$> metaType v) ++ ">"
  let solutions = [(sv v, pretty $ fmap (unvar show sv) <$> msol) | (v, msol) <- zip vsl pvs]
  return $ pretty (unvar show sv <$> x) <> text ", vars: " <> pretty solutions

tr :: (HasRelevance a, HasPlicitness a, Eq a, Functor f, Foldable f, Pretty (f String), Show v)
   => String -> f (Var v (MetaVar s d a v)) -> TCM s v' ()
tr s x = do
  i <- gets tcIndent
  r <- showMeta x
  Monad.log $ mconcat (replicate i "| ") ++ "--" ++ s ++ ": " ++ showWide r

existsAtLevel :: NameHint -> CoreM s d a v -> d -> Level -> TCM s v' (MetaVar s d a v)
existsAtLevel hint typ dat l = do
  i   <- fresh
  ref <- liftST $ newSTRef $ Left l
  Monad.log $ "exists: " ++ show i
  return $ MetaVar i typ hint dat (Just ref)

exists :: NameHint -> CoreM s d a v -> d -> TCM s v' (MetaVar s d a v)
exists hint typ dat = existsAtLevel hint typ dat =<< level

existsVar :: Applicative g => NameHint -> CoreM s d a v -> d -> TCM s v' (g (Var v (MetaVar s d a v)))
existsVar hint typ dat = pure . F <$> exists hint typ dat

existsVarAtLevel :: Applicative g => NameHint -> CoreM s d a v -> d -> Level -> TCM s v' (g (Var v (MetaVar s d a v)))
existsVarAtLevel hint typ dat l = pure . F <$> existsAtLevel hint typ dat l

forall_ :: NameHint -> CoreM s d a v -> d -> TCM s v' (MetaVar s d a v)
forall_ hint typ dat = do
  i <- fresh
  Monad.log $ "forall: " ++ show i
  return $ MetaVar i typ hint dat Nothing

forallVar :: Applicative g => NameHint -> CoreM s d a v -> d -> TCM s v' (g (Var v (MetaVar s d a v)))
forallVar hint typ dat = pure . F <$> forall_ hint typ dat

solution :: Exists s d a v -> TCM s v' (Either Level (CoreM s d a v))
solution = liftST . readSTRef

solve :: Exists s d a v -> CoreM s d a v -> TCM s v' ()
solve r x = liftST $ writeSTRef r $ Right x

refineIfSolved :: Exists s d a v -> CoreM s d a v -> (CoreM s d a v -> TCM s v' (CoreM s d a v)) -> TCM s v' (CoreM s d a v)
refineIfSolved r d f = do
  sol <- solution r
  case sol of
    Left _  -> return d
    Right e -> do
      e' <- f e
      solve r e'
      return e'

letMeta :: NameHint -> CoreM s d a v -> CoreM s d a v -> d -> TCM s v' (MetaVar s d a v)
letMeta hint expr typ dat = do
  i   <- fresh
  ref <- liftST $ newSTRef $ Right expr
  return $ MetaVar i typ hint dat (Just ref)

letVar :: Applicative g => NameHint -> CoreM s d a v -> CoreM s d a v -> d -> TCM s v' (g (Var v (MetaVar s d a v)))
letVar hint expr typ dat = pure . F <$> letMeta hint expr typ dat

foldMapM :: (Foldable f, Monoid m) => (MetaVar s d a v -> m) -> f (Var v (MetaVar s d a v)) -> TCM s v' m
foldMapM f = foldrM go mempty
  where
    go (B _) m = pure m
    go (F v) m = (<> m) . (<> f v) <$> do
      tvs <- foldMapM f $ metaType v
      (<> tvs) <$> case metaRef v of
        Just r -> do
          sol <- solution r
          case sol of
            Left _  -> return mempty
            Right c -> foldMapM f c
        Nothing -> return $ f v <> m

abstractM :: (Show d, Show a, Show v)
          => (MetaVar s d a v -> Maybe b)
          -> CoreM s d a v
          -> TCM s v' (ScopeM b Core.Expr s d a v)
abstractM f e = do
  e' <- freeze e
  changed <- liftST $ newSTRef False
  Scope . join <$> traverse (go changed) e'
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

abstract1M :: (Show d, Show a, Show v)
           => MetaVar s d a v
           -> CoreM s d a v
           -> TCM s v' (ScopeM () Core.Expr s d a v)
abstract1M v e = do
  Monad.log $ "abstracting " ++ show (metaId v)
  abstractM (\v' -> if v == v' then Just () else Nothing) e

freeze :: CoreM s d a v -> TCM s v' (CoreM s d a v)
freeze e = join <$> traverse go e
  where
    go (F v@(metaRef -> Just r)) = either (const $ do mt <- freeze (metaType v); return $ return $ F v {metaType = mt})
                                          freeze =<< solution r
    go v                         = return $ return v
