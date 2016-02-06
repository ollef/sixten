{-# LANGUAGE RecursiveDo, ViewPatterns #-}
module Meta where

import Control.Applicative
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
import qualified Data.Vector as V

import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete as Concrete
import qualified Syntax.Lambda as Lambda
import TCM
import Util

type Exists s = STRef s (Either Level (AbstractM s))

data MetaVar s = MetaVar
  { metaId    :: !Int
  , metaType  :: AbstractM s
  , metaHint  :: !NameHint
  , metaRef   :: !(Maybe (Exists s))
  }

type ConcreteM s = Concrete.Expr (MetaVar s)
type AbstractM s = Abstract.Expr (MetaVar s)
type LambdaM s = Lambda.Expr (MetaVar s)
type ScopeM b f s = Scope b f (MetaVar s)
type BranchesM c f s = Branches c f (MetaVar s)

instance Eq (MetaVar s) where
  (==) = (==) `on` metaId

instance Ord (MetaVar s) where
  compare = compare `on` metaId

instance Hashable (MetaVar s) where
  hashWithSalt s = hashWithSalt s . metaId

instance Show (MetaVar s) where
  showsPrec d (MetaVar i t h _) = showParen (d > 10) $
    showString "Meta" . showChar ' ' . showsPrec 11 i .
    showChar ' ' . showsPrec 11 t . showChar ' ' . showsPrec 11 h .
    showChar ' ' . showString "<Ref>"

showMeta
  :: (Functor f, Foldable f, Pretty (f String))
  => f (MetaVar s)
  -> TCM s Doc
showMeta x = do
  vs <- foldMapM S.singleton x
  let p (metaRef -> Just r) = solution r
      p _                   = return $ Left $ Level (-1)
  let vsl = S.toList vs
  pvs <- T.mapM p vsl
  let sv v = "$" ++ fromMaybe "" (fromText <$> unHint (metaHint v)) ++ (if isJust $ metaRef v then "∃" else "")
          ++ show (metaId v) -- ++ ":"
          -- ++ show (pretty $ sv <$> metaType v) ++ ">"
  let solutions = [(sv v, pretty $ sv <$> metaType v, pretty $ fmap sv <$> msol) | (v, msol) <- zip vsl pvs]
  return $ pretty (sv <$> x) <> text ", vars: " <> pretty solutions

tr :: (Functor f, Foldable f, Pretty (f String))
   => String
   -> f (MetaVar s)
   -> TCM s ()
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

existsAtLevel :: NameHint -> AbstractM s -> Level -> TCM s (MetaVar s)
existsAtLevel hint typ l = do
  i   <- fresh
  ref <- liftST $ newSTRef $ Left l
  TCM.log $ "exists: " ++ show i
  return $ MetaVar i typ hint (Just ref)

exists :: NameHint -> AbstractM s -> TCM s (MetaVar s)
exists hint typ = existsAtLevel hint typ =<< level

existsVar :: Applicative g => NameHint -> AbstractM s -> TCM s (g (MetaVar s))
existsVar hint typ = pure <$> exists hint typ

existsVarAtLevel :: Applicative g => NameHint -> AbstractM s -> Level -> TCM s (g (MetaVar s))
existsVarAtLevel hint typ l = pure <$> existsAtLevel hint typ l

forall_ :: NameHint -> AbstractM s -> TCM s (MetaVar s)
forall_ hint typ = do
  i <- fresh
  TCM.log $ "forall: " ++ show i
  return $ MetaVar i typ hint Nothing

forallVar :: Applicative g => NameHint -> AbstractM s -> TCM s (g (MetaVar s))
forallVar hint typ = pure <$> forall_ hint typ

solution :: Exists s -> TCM s (Either Level (AbstractM s))
solution = liftST . readSTRef

solve :: Exists s -> AbstractM s -> TCM s ()
solve r x = liftST $ writeSTRef r $ Right x

refineIfSolved :: Exists s -> AbstractM s -> (AbstractM s -> TCM s (AbstractM s)) -> TCM s (AbstractM s)
refineIfSolved r d f = do
  sol <- solution r
  case sol of
    Left _  -> return d
    Right e -> do
      e' <- f e
      solve r e'
      return e'

letMeta :: NameHint -> AbstractM s -> AbstractM s -> TCM s (MetaVar s)
letMeta hint expr typ = do
  i   <- fresh
  ref <- liftST $ newSTRef $ Right expr
  return $ MetaVar i typ hint (Just ref)

letVar :: Applicative g
       => NameHint -> AbstractM s -> AbstractM s -> TCM s (g (MetaVar s))
letVar hint expr typ = pure <$> letMeta hint expr typ

foldMapM :: (Foldable f, Monoid m)
         => (MetaVar s -> m) -> f (MetaVar s) -> TCM s m
foldMapM f = foldrM go mempty
  where
    go v m = (<> m) . (<> f v) <$> do
      case metaRef v of
        Just r -> do
          sol <- solution r
          case sol of
            Left _  -> foldMapM f $ metaType v
            Right c -> foldMapM f c
        Nothing -> return mempty

abstractM :: (MetaVar s -> Maybe b)
          -> AbstractM s
          -> TCM s (ScopeM b Abstract.Expr s)
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

abstract1M :: MetaVar s
           -> AbstractM s
           -> TCM s (ScopeM () Abstract.Expr s)
abstract1M v e = do
  TCM.log $ "abstracting " ++ show (metaId v)
  abstractM (\v' -> if v == v' then Just () else Nothing) e

abstractDefM
  :: (MetaVar s -> Maybe b)
  -> Definition Abstract.Expr (MetaVar s)
  -> AbstractM s
  -> TCM s ( Definition Abstract.Expr (Var b (MetaVar s))
           , ScopeM b Abstract.Expr s
           )
abstractDefM f (Definition e) t = do
  e' <- abstractM f e
  t' <- abstractM f t
  return (Definition $ fromScope e', t')
abstractDefM f (DataDefinition e) t = do
  e' <- abstractDataDefM f e t
  t' <- abstractM f t
  return (DataDefinition e', t')

abstractDataDefM
  :: (MetaVar s -> Maybe b)
  -> DataDef Abstract.Expr (MetaVar s)
  -> AbstractM s
  -> TCM s (DataDef Abstract.Expr (Var b (MetaVar s)))
abstractDataDefM f (DataDef cs) typ = mdo
  let inst = instantiateTele $ pure <$> vs
      vs = (\(_, _, _, v) -> v) <$> ps'
  typ' <- freeze typ
  ps' <- forTele (Abstract.telescope typ') $ \h p s -> do
    let is = inst s
    v <- forall_ h is
    return (h, p, is, v)
  let f' x = F <$> f x <|> B . Tele <$> V.elemIndex x vs
  acs <- forM cs $ \c -> traverse (fmap (toScope . fmap assoc . fromScope) . abstractM f' . inst) c
  return $ DataDef acs
  where
    assoc :: Var (Var a b) c -> Var a (Var b c)
    assoc = unvar (unvar B (F . B)) (F . F)

etaLamM
  :: NameHint
  -> Annotation
  -> Abstract.Expr (MetaVar s)
  -> Scope1 Abstract.Expr (MetaVar s)
  -> TCM s (Abstract.Expr (MetaVar s))
etaLamM n p t s = do
  s' <- freezeBound s
  return $ Abstract.etaLam n p t s'

freeze :: AbstractM s -> TCM s (AbstractM s)
freeze e = join <$> traverse go e
  where
    go v@(metaRef -> Just r) = either (const $ do mt <- freeze (metaType v); return $ pure v {metaType = mt})
                                          freeze =<< solution r
    go v                         = return $ pure v

freezeBound :: (Traversable (t Abstract.Expr), Bound t)
            => t Abstract.Expr (MetaVar s)
            -> TCM s (t Abstract.Expr (MetaVar s))
freezeBound e = (>>>= id) <$> traverse go e
  where
    go v@(metaRef -> Just r) = either (const $ do mt <- freeze (metaType v); return $ pure v {metaType = mt})
                                          freeze =<< solution r
    go v = return $ pure v
