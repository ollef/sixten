{-# LANGUAGE DefaultSignatures, FlexibleInstances, MultiParamTypeClasses, RecursiveDo, ViewPatterns, OverloadedStrings, TypeFamilies #-}
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
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Prelude.Extras

import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete as Concrete
import qualified Syntax.SLambda as SLambda
import TCM
import Util

class Eq v => MetaVary e v where
  type MetaData e v
  forall :: NameHint -> MetaData e v -> e v -> TCM v
  default forall :: (v ~ MetaVar e) => NameHint -> MetaData e (MetaVar e) -> e (MetaVar e) -> TCM (MetaVar e)
  forall hint _a typ = do
    i <- fresh
    TCM.log $ "forall: " <> fromString (show i)
    return $ MetaVar i typ hint Nothing
  refineVar :: v -> (e v -> TCM (e v)) -> TCM (e v)
  default refineVar :: (v ~ MetaVar e, Applicative e) => MetaVar e -> (e (MetaVar e) -> TCM (e (MetaVar e))) -> TCM (e (MetaVar e))
  refineVar v@(metaRef -> Nothing) _ = return $ pure v
  refineVar v@(metaRef -> Just r) f = refineIfSolved r (pure v) f
  refineVar _ _ = error "refineVar impossible"
  metaVarType :: v -> e v
  default metaVarType :: (v ~ MetaVar e) => MetaVar e -> e (MetaVar e)
  metaVarType = metaType

instance MetaVary Unit (MetaVar Unit) where
  type MetaData Unit (MetaVar Unit) = ()
  refineVar _ _ = return Unit

type Exists e = STRef (World TCM) (Either Level (e (MetaVar e)))

data MetaVar e = MetaVar
  { metaId   :: !Int
  , metaType :: e (MetaVar e)
  , metaHint :: !NameHint
  , metaRef  :: !(Maybe (Exists e))
  }

instance MetaVary Concrete.Expr (MetaVar Concrete.Expr) where
  type MetaData Concrete.Expr (MetaVar Concrete.Expr) = Plicitness

instance MetaVary (Abstract.Expr a) (MetaVar (Abstract.Expr a)) where
  type MetaData (Abstract.Expr a) (MetaVar (Abstract.Expr a)) = a

type ConcreteM = Concrete.Expr (MetaVar Abstract.ExprP)
type AbstractM = Abstract.ExprP (MetaVar Abstract.ExprP)
type AbstractE = Abstract.ExprE (MetaVar Abstract.ExprE)
type LambdaM = SLambda.Expr (MetaVar Abstract.ExprE)
type SLambdaM = SLambda.SExpr (MetaVar Abstract.ExprE)
type ScopeM b f = Scope b f (MetaVar Abstract.ExprP)
type BranchesM c a f = Branches c a f (MetaVar Abstract.ExprP)
type SimpleBranchesM c f = SimpleBranches c f (MetaVar Abstract.ExprE)

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
  e' <- zonk e
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
      unless (S.null mftfvs)
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
  :: Show a
  => MetaVar (Abstract.Expr a)
  -> Abstract.Expr a (MetaVar (Abstract.Expr a))
  -> TCM (Scope () (Abstract.Expr a) (MetaVar (Abstract.Expr a)))
abstract1M v e = do
  TCM.log $ "abstracting " <> fromString (show $ metaId v)
  abstractM (\v' -> if v == v' then Just () else Nothing) e

abstractDefM
  :: (MetaVar Abstract.ExprP -> Maybe b)
  -> Definition Abstract.ExprP (MetaVar Abstract.ExprP)
  -> AbstractM
  -> TCM ( Definition Abstract.ExprP (Var b (MetaVar Abstract.ExprP))
           , ScopeM b Abstract.ExprP
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
  :: (MetaVar Abstract.ExprP -> Maybe b)
  -> DataDef Abstract.ExprP (MetaVar Abstract.ExprP)
  -> AbstractM
  -> TCM (DataDef Abstract.ExprP (Var b (MetaVar Abstract.ExprP)))
abstractDataDefM f (DataDef cs) typ = mdo
  let inst = instantiateTele $ pure <$> vs
      vs = (\(_, _, _, v) -> v) <$> ps'
  typ' <- zonk typ
  ps' <- forMTele (telescope typ') $ \h a s -> do
    let is = inst s
    v <- forall h a is
    return (h, a, is, v)
  let f' x = F <$> f x <|> B . Tele <$> Vector.elemIndex x vs
  acs <- forM cs $ \c -> traverse (fmap (toScope . fmap assoc . fromScope) . abstractM f' . inst) c
  return $ DataDef acs
  where
    assoc :: Var (Var a b) c -> Var a (Var b c)
    assoc = unvar (unvar B (F . B)) (F . F)

zonkVar
  :: (Monad e, Traversable e)
  => MetaVar e
  -> TCM (e (MetaVar e))
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
  -> TCM (e (MetaVar e))
zonk = fmap join . traverse zonkVar

zonkBound
  :: (Monad e, Traversable e, Traversable (t e), Bound t)
  => t e (MetaVar e)
  -> TCM (t e (MetaVar e))
zonkBound = fmap (>>>= id) . traverse zonkVar

metaTelescope
  :: Monad e
  => Vector (a, MetaVar e)
  -> Telescope Scope a e (MetaVar e)
metaTelescope vs =
  Telescope
  $ (\(a, v) -> (metaHint v, a, abstract abstr $ metaType v))
  <$> vs
  where
    abstr = teleAbstraction $ snd <$> vs

metaTelescopeM
  :: (Monad e, Traversable e, Show1 e)
  => Vector (a, MetaVar e)
  -> TCM (Telescope Scope a e (MetaVar e))
metaTelescopeM vs =
  fmap Telescope $ forM vs $ \(a, v) -> do
    s <- abstractM abstr $ metaType v
    return (metaHint v, a, s)
  where
    abstr = teleAbstraction $ snd <$> vs
