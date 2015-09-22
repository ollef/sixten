{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Relevance where

import Bound
import Bound.Var
import Control.Monad.Except
import Control.Monad.ST.Class
import Control.Monad.State
import Data.Bifunctor
import Data.Hashable
import Data.Monoid
import Data.STRef
import Data.Function
import Data.Vector(Vector)
import qualified Data.Vector as V

import Annotation hiding (Relevance(..))
import qualified Annotation
import Core
import Monad
import Pretty
import Util

{-

All args to functions into type are irrelevant (indicated with '~'), e.g.
  ~(a : A) -> Type

All args of type Type or function into Type are irrelevant, e.g.
~(arg : Type)       -> B
~(arg : ~A -> Type) -> B

Args only used irrelevantly using the above rules are irrelevant, e.g. X in

forall ~{b : Type}~{X : b}{F : ~b -> Type}. F ~X -> F ~X

-}

data MetaRel s = MetaRel
  { metaRelId  :: Int
  , metaRelRef :: STRef s (Maybe (RelevanceM s))
  }

instance Show (MetaRel s) where
  showsPrec d (MetaRel i _) = showParen (d > 10) $
    showString "MetaRel " . showChar ' ' . showsPrec 11 i

freshMetaRel :: TCM s v (MetaRel s)
freshMetaRel = MetaRel <$> fresh <*> liftST (newSTRef Nothing)

instance Eq (MetaRel s) where (==) = (==) `on` metaRelId
instance Ord (MetaRel s) where compare = compare `on` metaRelId

data Relevance v
  = RVar v
  | Irrelevant
  | Relevant
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Relevance where
  pure = return
  (<*>) = ap

instance Monad Relevance where
  return = RVar
  RVar v >>= f = f v
  Relevant >>= _ = Relevant
  Irrelevant >>= _ = Irrelevant

fromRelevance :: Annotation.Relevance -> Relevance v
fromRelevance Annotation.Relevant = Relevant
fromRelevance Annotation.Irrelevant = Irrelevant

type RelevanceM s = Relevance (MetaRel s)

data Meta s v = Meta
  { metaId   :: Int
  , metaRel  :: RelevanceM s
  , metaType :: Output s v
  }

instance Show (Meta s v) where
  showsPrec d (Meta i _ _) = showParen (d > 10) $
    showString "Meta" . showChar ' ' . showsPrec 11 i

instance Eq (Meta s v) where (==) = (==) `on` metaId
instance Ord (Meta s v) where
  compare = compare `on` metaId

data MetaAnnotation s = MetaAnnotation (RelevanceM s) Plicitness
  deriving Eq

instance HasRelevance  (MetaAnnotation s) where
  relevance (MetaAnnotation r _) = case r of
    Relevant   -> Annotation.Relevant
    Irrelevant -> Annotation.Irrelevant
    RVar _     -> Annotation.Relevant

instance HasPlicitness (MetaAnnotation s) where
  plicitness (MetaAnnotation _ p) = p

relevanceM :: HasRelevance d => d -> RelevanceM s
relevanceM d = case relevance d of
  Annotation.Relevant -> Relevant
  Annotation.Irrelevant -> Irrelevant

toMetaAnnotation :: (HasRelevance d, HasPlicitness d) => d -> MetaAnnotation s
toMetaAnnotation d = MetaAnnotation (relevanceM d) (plicitness d)

fromMetaAnnotation :: MetaAnnotation s -> TCM s v Annotation
fromMetaAnnotation (MetaAnnotation r p) = Annotation <$> fromRelevanceM r <*> pure p

fromRelevanceM :: RelevanceM s -> TCM s v Annotation.Relevance
fromRelevanceM Relevant = return Annotation.Relevant
fromRelevanceM Irrelevant = return Annotation.Irrelevant
fromRelevanceM (RVar v) = do
  sol <- liftST $ readSTRef $ metaRelRef v
  case sol of
    Nothing -> return Annotation.Irrelevant
    Just r' -> fromRelevanceM r'

freshForall :: RelevanceM s -> Output s v -> TCM s v' (Meta s v)
freshForall r e = do
  i <- fresh
  return $ Meta i r e

type Input       s v   = Expr Plicitness (Var v (Meta s v))
type InputScope  s b v = Scope b (Expr Plicitness) (Var v (Meta s v))
type Output      s v   = Expr (MetaAnnotation s) (Var v (Meta s v))
type OutputScope s b v = Scope b (Expr (MetaAnnotation s)) (Var v (Meta s v))

tr :: (Pretty (f String), Functor f, Show v) => String -> f (Var v (Meta s v)) -> TCM s v ()
tr s x = do
  i <- gets tcIndent
  let r = pretty $ fmap show x
  Monad.log $ mconcat (replicate i "| ") ++ "--" ++ s ++ ": " ++ showWide r

returnsType :: HasPlicitness p => Expr p v -> Bool
returnsType expr = case expr of
  Var _  -> False
  Type   -> True
  Pi _ _ _ s  -> returnsType $ fromScope s
  Lam {} -> False
  App e1 p e2 -> case e1 of
    Lam _ p' _ s | plicitness p == plicitness p' -> returnsType $ instantiate1 e2 s
    _ -> False
  Case _ _ -> undefined -- TODO

makeIrrelevant :: HasPlicitness p => Expr p v -> Expr (MetaAnnotation s) v
makeIrrelevant expr = case expr of
  Var v -> Var v
  Type -> Type
  Pi  x p t s -> Pi  x (meta p) (makeIrrelevant t) (makeScopeIrrelevant s)
  Lam x p t s -> Lam x (meta p) (makeIrrelevant t) (makeScopeIrrelevant s)
  App e1 p e2 -> App (makeIrrelevant e1) (meta p) (makeIrrelevant e2)
  Case _ _ -> undefined -- TODO
  where
    meta = MetaAnnotation Irrelevant . plicitness
    makeScopeIrrelevant = toScope . makeIrrelevant . fromScope

inferArg :: (Hashable v, Ord v, Show v)
          => Input s v -> TCM s v (Output s v, RelevanceM s)
inferArg typ
  | returnsType typ = return (makeIrrelevant typ, Irrelevant)
  | otherwise = do
    argType' <- check typ Type Irrelevant
    rel <- freshMetaRel
    return (argType', pure rel)

inferTop :: (Hashable v, Ord v, Show v)
          => Input s v -> TCM s v (Output s v, RelevanceM s)
inferTop typ
  | returnsType typ = return (makeIrrelevant typ, Irrelevant)
  | otherwise = do
    (argType', _) <- infer typ Irrelevant
    return (argType', Relevant)

leRel :: RelevanceM s -> RelevanceM s -> TCM s v ()
leRel rel1 rel2 = case (rel1, rel2) of
  (Irrelevant, _) -> return ()
  (_, Relevant) -> return ()
  (RVar v1, RVar v2)
    | v1 == v2 -> return ()
    | otherwise -> do
      sol1 <- liftST $ readSTRef $ metaRelRef v1
      sol2 <- liftST $ readSTRef $ metaRelRef v2
      case (sol1, sol2) of
        (Just rel1', _) -> leRel rel1' rel2
        (_, Just rel2') -> leRel rel1 rel2'
        (Nothing, Nothing) -> liftST $ writeSTRef (metaRelRef v2) $ Just rel1
  (RVar v1, _) -> do
    sol <- liftST $ readSTRef $ metaRelRef v1
    case sol of
      Just rel1' -> leRel rel1' rel2
      Nothing -> liftST $ writeSTRef (metaRelRef v1) $ Just rel2
  (_, RVar v2) -> do
    sol <- liftST $ readSTRef $ metaRelRef v2
    case sol of
      Just rel2' -> leRel rel1 rel2'
      Nothing -> liftST $ writeSTRef (metaRelRef v2) $ Just rel1
  _ -> throwError $ "leRel" ++ show (rel1, rel2)

unifyRel :: RelevanceM s -> RelevanceM s -> TCM s v ()
unifyRel rel1 rel2 = case (rel1, rel2) of
  (RVar v1, RVar v2)
    | v1 == v2 -> return ()
    | otherwise -> do
      sol1 <- liftST $ readSTRef $ metaRelRef v1
      sol2 <- liftST $ readSTRef $ metaRelRef v2
      case (sol1, sol2) of
        (Just rel1', _) -> unifyRel rel1' rel2
        (_, Just rel2') -> unifyRel rel1 rel2'
        (Nothing, Nothing) -> liftST $ writeSTRef (metaRelRef v2) $ Just rel1
  (RVar v1, _) -> do
    sol <- liftST $ readSTRef $ metaRelRef v1
    case sol of
      Just rel1' -> unifyRel rel1' rel2
      Nothing -> liftST $ writeSTRef (metaRelRef v1) $ Just rel2
  (_, RVar v2) -> do
    sol <- liftST $ readSTRef $ metaRelRef v2
    case sol of
      Just rel2' -> unifyRel rel1 rel2'
      Nothing -> liftST $ writeSTRef (metaRelRef v2) $ Just rel1
  (Irrelevant, Irrelevant) -> return ()
  (Relevant, Relevant) -> return ()
  _ -> throwError "unifyRel"

infer :: (Hashable v, Ord v, Show v)
      => Input s v -> RelevanceM s -> TCM s v (Output s v, Output s v)
infer expr surroundingRel = case expr of
  Var (F v) -> do
    leRel surroundingRel $ metaRel v
    return (Var $ F v, metaType v)
  Var (B v)   -> do
    (_, t, a) <- context v
    leRel surroundingRel $ relevanceM a
    return (Var $ B v, bimap toMetaAnnotation B t)
  Type        -> return (Type, Type)
  Pi x p t1 s -> do
    (t1', t1rel) <- inferArg t1
    v     <- freshForall t1rel t1'
    e'    <- check (instantiate1 (pure $ F v) s) Type surroundingRel
    return ( Pi x (MetaAnnotation t1rel p) t1' $ abstract1 (F v) e'
           , Type
           )
  Lam x p t1 s -> do
    (t1', t1rel) <- inferArg t1
    v         <- freshForall t1rel t1'
    (e', t2') <- infer (instantiate1 (pure $ F v) s) surroundingRel
    return ( Lam x (MetaAnnotation t1rel p) t1' $ abstract1 (F v) e'
           , Pi  x (MetaAnnotation t1rel p) t1' $ abstract1 (F v) t2'
           )
  App e1 p e2 -> do
    (e1', ft) <- infer e1 surroundingRel
    case ft of
      Pi _ rp@(MetaAnnotation rel p') argt s | plicitness p == p' -> do
        e2' <- check e2 argt rel
        return (App e1' rp e2', instantiate1 e2' s)
      _ -> throwError "infer relevance infer1"
  _ -> throwError "infer relevance infer2"

check :: (Hashable v, Ord v, Show v)
      => Input s v -> Output s v -> RelevanceM s -> TCM s v (Output s v)
check expr typ rel = do
  (expr', typ') <- infer expr rel
  subtype expr' typ' typ

subtype :: (Hashable v, Ord v, Show v)
        => Output s v -> Output s v -> Output s v -> TCM s v' (Output s v)
subtype expr typ1 typ2 = case (typ1, typ2) of
  (Var (F v1), Var (F v2)) -> do
    leRel (metaRel v2) (metaRel v1)
    return expr
  (Pi h1 (MetaAnnotation r1 p1) t1 s1,  Pi h2 (MetaAnnotation r2 p2) t2 s2) | p1 == p2 -> do
    x2 <- freshForall r1 t2
    x1 <- subtype (return $ F x2) t2 t1
    expr2 <- subtype (betaApp expr (MetaAnnotation r1 p1) x1)
                     (instantiate1 x1 s1)
                     (instantiate1 (return $ F x2) s2)
    return $ etaLam (h1 <> h2) (MetaAnnotation r2 p2) t2 (abstract1 (F x2) expr2)
  _ -> do unify typ1 typ2; return expr

unify :: (Eq v, Show v) => Output s v -> Output s v -> TCM s v' ()
unify typ1 typ2 | typ1 == typ2 = return ()
unify typ1 typ2 = case (typ1, typ2) of
  (Var (F v1), Var (F v2)) -> unifyRel (metaRel v1) (metaRel v2)
  (App t1 (MetaAnnotation r1 p1) t1', App t2 (MetaAnnotation r2 p2) t2') | p1 == p2 -> do
    unifyRel r1 r2
    unify t1 t2
    unify t2' t1'
  _ -> throwError $ "rel subtype: " ++ show (pretty (show <$> typ1, show <$> typ2))

checkRecursiveDefs :: (Hashable v, Ord v, Show v)
                   => Vector (InputScope s Int v, InputScope s Int v)
                   -> TCM s v (Vector (OutputScope s Int v, OutputScope s Int v, RelevanceM s))
checkRecursiveDefs ds = case traverse unusedScope $ snd <$> ds of
  Nothing -> throwError "Mutually recursive types not supported"
  Just ts -> do
    evs <- V.forM ts $ \t -> do
      (t', rel) <- inferTop t
      ev <- freshForall rel t'
      return (ev, t', rel)
    let instantiatedDs = flip V.imap ds $ \i (s, _) ->
          (evs V.! i, instantiate (pure . pure . (\(ev, _, _) -> ev) . (evs V.!)) s)
    checkedDs <- V.forM instantiatedDs $ \((m, t, rel), e) -> do
      (e', t') <- infer e rel
      e'' <- subtype e' t' t
      return (m, e'', t)
    V.forM checkedDs $ \(m, e, t) -> do
      let f  = unvar (const Nothing) $ flip V.elemIndex $ (\(ev, _, _) -> ev) <$> evs
          s  = abstract f e
          st = abstract f t
      return (s, st, metaRel m)
