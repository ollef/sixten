{-# LANGUAGE RecursiveDo, ViewPatterns, OverloadedStrings #-}
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
import Data.String
import qualified Data.Traversable as T
import qualified Data.Vector as V
import Prelude.Extras

import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete as Concrete
import qualified Syntax.SLambda as SLambda
import TCM
import Util

type Exists e = STRef (World TCM) (Either Level (e (MetaVar e)))

data MetaVar e = MetaVar
  { metaId   :: !Int
  , metaType :: e (MetaVar e)
  , metaHint :: !NameHint
  , metaRef  :: !(Maybe (Exists e))
  }

type ConcreteM = Concrete.Expr (MetaVar Abstract.Expr)
type AbstractM = Abstract.Expr (MetaVar Abstract.Expr)
type LambdaM = SLambda.Expr (MetaVar Abstract.Expr)
type SLambdaM = SLambda.SExpr (MetaVar Abstract.Expr)
type ScopeM b f = Scope b f (MetaVar Abstract.Expr)
type BranchesM c f = Branches c f (MetaVar Abstract.Expr)
type SimpleBranchesM c f = SimpleBranches c f (MetaVar Abstract.Expr)

instance Eq (MetaVar e) where
  (==) = (==) `on` metaId

instance Ord (MetaVar e) where
  compare = compare `on` metaId

instance Hashable (MetaVar e) where
  hashWithSalt s = hashWithSalt s . metaId

instance Show1 e => Show (MetaVar e) where
  showsPrec d (MetaVar i t h _) = showParen (d > 10) $
    showString "Meta" . showChar ' ' . showsPrec 11 i .
    showChar ' ' . showsPrec1 11 t . showChar ' ' . showsPrec 11 h .
    showChar ' ' . showString "<Ref>"

showMeta
  :: (Functor e, Foldable e, Functor f, Foldable f, Pretty (f String), Pretty (e String))
  => f (MetaVar e)
  -> TCM Doc
showMeta x = do
  vs <- foldMapM S.singleton x
  let p (metaRef -> Just r) = solution r
      p _                   = return $ Left $ Level (-1)
  let vsl = S.toList vs
  pvs <- T.mapM p vsl
  let sv v = "$" ++ fromMaybe "" (fromText <$> unNameHint (metaHint v)) ++ (if isJust $ metaRef v then "∃" else "")
          ++ show (metaId v) -- ++ ":"
          -- ++ show (pretty $ sv <$> metaType v) ++ ">"
  let solutions = [(sv v, pretty $ sv <$> metaType v, pretty $ fmap sv <$> msol) | (v, msol) <- zip vsl pvs]
  return $ pretty (sv <$> x) <> text ", vars: " <> pretty solutions

tr :: (Functor e, Foldable e, Functor f, Foldable f, Pretty (f String), Pretty (e String))
   => String
   -> f (MetaVar e)
   -> TCM ()
tr s x = do
  i <- gets tcIndent
  r <- showMeta x
  TCM.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide r

trp :: Pretty a => String -> a -> TCM ()
trp s x = do
  i <- gets tcIndent
  TCM.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide (pretty x)

trs :: Show a => String -> a -> TCM ()
trs s x = do
  i <- gets tcIndent
  TCM.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> fromString (show x)

existsAtLevel :: NameHint -> e (MetaVar e) -> Level -> TCM (MetaVar e)
existsAtLevel hint typ l = do
  i   <- fresh
  ref <- liftST $ newSTRef $ Left l
  TCM.log $ "exists: " <> fromString (show i)
  return $ MetaVar i typ hint (Just ref)

exists :: NameHint -> e (MetaVar e) -> TCM (MetaVar e)
exists hint typ = existsAtLevel hint typ =<< level

existsVar
  :: Applicative g
  => NameHint
  -> e (MetaVar e)
  -> TCM (g (MetaVar e))
existsVar hint typ = pure <$> exists hint typ

existsVarAtLevel
  :: Applicative g
  => NameHint
  -> e (MetaVar e)
  -> Level
  -> TCM (g (MetaVar e))
existsVarAtLevel hint typ l = pure <$> existsAtLevel hint typ l

forall_ :: NameHint -> e (MetaVar e) -> TCM (MetaVar e)
forall_ hint typ = do
  i <- fresh
  TCM.log $ "forall: " <> fromString (show i)
  return $ MetaVar i typ hint Nothing

forallVar
  :: Applicative g
  => NameHint
  -> e (MetaVar e)
  -> TCM (g (MetaVar e))
forallVar hint typ = pure <$> forall_ hint typ

solution :: Exists e -> TCM (Either Level (e (MetaVar e)))
solution = liftST . readSTRef

solve :: Exists e -> e (MetaVar e) -> TCM ()
solve r x = liftST $ writeSTRef r $ Right x

refineIfSolved
  :: Exists e
  -> e (MetaVar e)
  -> (e (MetaVar e) -> TCM (e (MetaVar e)))
  -> TCM (e (MetaVar e))
refineIfSolved r d f = do
  sol <- solution r
  case sol of
    Left _  -> return d
    Right e -> do
      e' <- f e
      solve r e'
      return e'

letMeta
  :: NameHint
  -> e (MetaVar e)
  -> e (MetaVar e)
  -> TCM (MetaVar e)
letMeta hint expr typ = do
  i   <- fresh
  TCM.log $ "let: " <> fromString (show i)
  ref <- liftST $ newSTRef $ Right expr
  return $ MetaVar i typ hint (Just ref)

foldMapM
  :: (Foldable e, Foldable f, Monoid m)
  => (MetaVar e -> m)
  -> f (MetaVar e)
  -> TCM m
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
  -> TCM (Scope b e (MetaVar e))
abstractM f e = do
  e' <- freeze e
  changed <- liftST $ newSTRef False
  Scope . join <$> traverse (go changed) e'
  where
    -- go :: STRef s Bool -> MetaVar s
    --    -> TCM (Expr (Var () (Expr (MetaVar s))))
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

abstract1M :: MetaVar Abstract.Expr
           -> AbstractM
           -> TCM (ScopeM () Abstract.Expr)
abstract1M v e = do
  TCM.log $ "abstracting " <> fromString (show $ metaId v)
  abstractM (\v' -> if v == v' then Just () else Nothing) e

abstractDefM
  :: (MetaVar Abstract.Expr -> Maybe b)
  -> Definition Abstract.Expr (MetaVar Abstract.Expr)
  -> AbstractM
  -> TCM ( Definition Abstract.Expr (Var b (MetaVar Abstract.Expr))
           , ScopeM b Abstract.Expr
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
  :: (MetaVar Abstract.Expr -> Maybe b)
  -> DataDef Abstract.Expr (MetaVar Abstract.Expr)
  -> AbstractM
  -> TCM (DataDef Abstract.Expr (Var b (MetaVar Abstract.Expr)))
abstractDataDefM f (DataDef cs) typ = mdo
  let inst = instantiateTele $ pure <$> vs
      vs = (\(_, _, _, v) -> v) <$> ps'
  typ' <- freeze typ
  ps' <- forMTele (telescope typ') $ \h p s -> do
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
  -> Abstract.Expr (MetaVar Abstract.Expr)
  -> Scope1 Abstract.Expr (MetaVar Abstract.Expr)
  -> TCM (Abstract.Expr (MetaVar Abstract.Expr))
etaLamM n p t s = do
  s' <- freezeBound s
  return $ Abstract.etaLam n p t s'

freeze :: (Monad e, Traversable e) => e (MetaVar e) -> TCM (e (MetaVar e))
freeze e = join <$> traverse go e
  where
    go v@(metaRef -> Just r) = either (const $ do mt <- freeze (metaType v); return $ pure v {metaType = mt})
                                          freeze =<< solution r
    go v                         = return $ pure v

freezeBound :: (Monad e, Traversable e, Traversable (t e), Bound t)
            => t e (MetaVar e)
            -> TCM (t e (MetaVar e))
freezeBound e = (>>>= id) <$> traverse go e
  where
    go v@(metaRef -> Just r) = either (const $ do mt <- freeze (metaType v); return $ pure v {metaType = mt})
                                          freeze =<< solution r
    go v = return $ pure v
