{-# LANGUAGE ViewPatterns #-}
module Meta where

import Bound
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.ST.Class
import Data.Either
import Data.Foldable
import Data.Function
import Data.Maybe
import Data.Monoid
import qualified Data.Set as S
import Data.STRef
import qualified Data.Traversable as T

import qualified Core
import qualified Input
import Monad
import Pretty
import Util

showMeta :: (Functor f, Foldable f, Pretty (f String)) => f (MetaVar s) -> TCM s Doc
showMeta x = do
  vs <- foldMapM S.singleton x
  let p (metaRef -> Just r) = either (const Nothing) Just <$> solution r
      p _                   = return Nothing
  let vsl = S.toList vs
  pvs <- T.mapM p vsl
  let sv v = "[" ++ (if isJust $ metaRef v then "∃" else "") ++ show (metaId v) ++ ":" ++ show (pretty $ sv <$> metaType v) ++ "]"
  let solutions = [(sv v, pretty $ fmap sv <$> msol) | (v, msol) <- zip vsl pvs]
  return $ pretty (sv <$> x) <> text ", vars: " <> pretty solutions

tr :: (Functor f, Foldable f, Pretty (f String)) => String -> f (MetaVar s) -> TCM s ()
tr s x = do
  i <- gets tcIndent
  r <- showMeta x
  Monad.log $ mconcat (replicate i "| ") ++ "--" ++ s ++ ": " ++ showWide r
  return ()

modifyIndent :: (Int -> Int) -> TCM s ()
modifyIndent f = modify $ \s -> s {tcIndent = f $ tcIndent s}

type Input s = Input.Expr (MetaVar s)
type Core  s = Core.Expr  (MetaVar s)

type Exists s = STRef s (Either Level (Core s))

data MetaVar s = MetaVar
  { metaId    :: {-# UNPACK #-} !Int
  , metaType  :: Core s
  , metaHint  :: {-# UNPACK #-} !NameHint
  , metaRef   :: {-# UNPACK #-} !(Maybe (Exists s))
  }

instance Eq (MetaVar s) where
  (==) = (==) `on` metaId

instance Ord (MetaVar s) where
  compare = compare `on` metaId

instance Show (MetaVar s) where
  showsPrec d (MetaVar i a h _) = showParen (d > 10) $
    showString "Meta" . showChar ' ' . showsPrec 11 i .
    showChar ' ' . showsPrec 11 a . showChar ' ' . showsPrec 11 h .
    showChar ' ' . showString "<Ref>"

freshExists :: NameHint -> Core s -> TCM s (MetaVar s)
freshExists h a = freshExistsL h a =<< level

freshExistsL :: NameHint -> Core s -> Level -> TCM s (MetaVar s)
freshExistsL h a l = do
  i   <- fresh
  ref <- liftST $ newSTRef $ Left l
  Monad.log $ "exists: " ++ show i
  return $ MetaVar i a h (Just ref)

freshExistsV :: Monad g => NameHint -> Core s -> TCM s (g (MetaVar s))
freshExistsV h a = return <$> freshExists h a

freshExistsLV :: Monad g => NameHint -> Core s -> Level -> TCM s (g (MetaVar s))
freshExistsLV h a l = return <$> freshExistsL h a l

freshForall :: NameHint -> Core s -> TCM s (MetaVar s)
freshForall h a = do
  i <- fresh
  Monad.log $ "forall: " ++ show i
  return $ MetaVar i a h Nothing

freshForallV :: Monad g => NameHint -> Core s -> TCM s (g (MetaVar s))
freshForallV h a = return <$> freshForall h a

refine :: Exists s -> Core s -> (Core s -> TCM s (Core s)) -> TCM s (Core s)
refine r d f = solution r >>=
  either (const $ return d) (\e -> do
    e' <- f e
    liftST $ writeSTRef r (Right e')
    return e'
  )

solution :: Exists s -> TCM s (Either Level (Core s))
solution = liftST . readSTRef

solve :: Exists s -> Core s -> TCM s ()
solve r x = do
  whenM (isRight <$> solution r) $ throwError "Trying to solve a variable that's already solved"
  liftST $ writeSTRef r $ Right x

refineSolved :: Exists s -> Core s -> TCM s ()
refineSolved r x = do
  whenM (isLeft <$> solution r) $ throwError "Trying to refine a variable that's not solved"
  liftST $ writeSTRef r $ Right x

freshLet :: NameHint -> Core s -> Core s -> TCM s (MetaVar s)
freshLet h e t = do
  i   <- fresh
  ref <- liftST $ newSTRef $ Right e
  return $ MetaVar i t h (Just ref)

freshLetV :: Monad g => NameHint -> Core s -> Core s -> TCM s (g (MetaVar s))
freshLetV h e t = return <$> freshLet h e t

foldMapM :: (Foldable f, Monoid m) => (MetaVar s -> m) -> f (MetaVar s) -> TCM s m
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

abstract1M :: MetaVar s -> Core s -> TCM s (Scope1 Core.Expr (MetaVar s))
abstract1M v e = do
  Monad.log $ "abstracting " ++ show (metaId v)
  e' <- freeze e
  changed <- liftST $ newSTRef False
  (Scope . join) <$> traverse (go changed) e'
  where
    -- go :: STRef s Bool -> MetaVar s
    --    -> TCM s (Expr (Var () (Expr (MetaVar s))))
    go changed v' | v == v' = do
      liftST $ writeSTRef changed True
      return $ return $ B ()
    go changed v'@(metaRef -> Just r) = do
      tfvs <- foldMapM S.singleton $ metaType v'
      when (v `S.member` tfvs) $ Monad.log $ "escape " ++ show (metaId v)
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
    free = return . return . return . return

freeze :: Core s -> TCM s (Core s)
freeze e = join <$> traverse go e
  where
    go v@(metaRef -> Just r) = either (const $ do mt <- freeze (metaType v); return $ return v {metaType = mt}) freeze =<< solution r
    go v                     = return $ return v
