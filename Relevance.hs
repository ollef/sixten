{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Relevance where

import Bound
import Bound.Var
import Control.Monad.Except
import Control.Monad.ST.Class
import Data.Bifunctor
import Data.Bitraversable
import Data.Hashable
import Data.Monoid
import Data.STRef
import Data.Function
import Data.Vector(Vector)
import qualified Data.Vector as V

import Annotation
import Core
import Hint
import Meta
import Monad
import Normalise
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

data RelevanceV v
  = RVar v
  | Relevance Relevance
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative RelevanceV where
  pure = return
  (<*>) = ap

instance Monad RelevanceV where
  return = RVar
  RVar v >>= f = f v
  Relevance r >>= _ = Relevance r

type RelevanceM s = RelevanceV (MetaRel s)

data MetaAnnotation s = MetaAnnotation
  { metaRelevance  :: RelevanceM s
  , metaPlicitness :: Plicitness
  } deriving (Eq, Show)

instance HasRelevance  (MetaAnnotation s) where
  relevance (MetaAnnotation r _) = case r of
    Relevance rel -> rel
    RVar _        -> Relevant

instance HasPlicitness (MetaAnnotation s) where
  plicitness (MetaAnnotation _ p) = p

toRelevanceM :: HasRelevance d => d -> RelevanceM s
toRelevanceM d = case relevance d of
  Annotation.Relevant   -> Relevance Relevant
  Annotation.Irrelevant -> Relevance Irrelevant

toMetaAnnotation :: (HasRelevance d, HasPlicitness d) => d -> MetaAnnotation s
toMetaAnnotation d = MetaAnnotation (toRelevanceM d) (plicitness d)

fromMetaAnnotation :: MetaAnnotation s -> TCM s v Annotation
fromMetaAnnotation (MetaAnnotation r p) = Annotation <$> fromRelevanceM r <*> pure p

fromRelevanceM :: RelevanceM s -> TCM s v Annotation.Relevance
fromRelevanceM (Relevance r) = return r
fromRelevanceM (RVar v) = do
  sol <- liftST $ readSTRef $ metaRelRef v
  case sol of
    Nothing -> return Annotation.Irrelevant
    Just r' -> fromRelevanceM r'

type Input       s v   = Core.Expr Plicitness (Var v (MetaVar s (RelevanceM s) (MetaAnnotation s) v))
type InputScope  s b v = Scope b (Core.Expr Plicitness) (Var v (MetaVar s (RelevanceM s) (MetaAnnotation s) v))
type Output      s v   = CoreM s (RelevanceM s) (MetaAnnotation s) v
type OutputScope s b v = ScopeM b Expr s (RelevanceM s) (MetaAnnotation s) v

leRel :: RelevanceM s -> RelevanceM s -> TCM s v ()
leRel rel1 rel2 = case (rel1, rel2) of
  (Relevance Irrelevant, _) -> return ()
  (_, Relevance Relevant) -> return ()
  (RVar v1, RVar v2)
    | v1 == v2 -> return ()
    | otherwise -> do
      sol1 <- liftST $ readSTRef $ metaRelRef v1
      sol2 <- liftST $ readSTRef $ metaRelRef v2
      case (sol1, sol2) of
        (Just rel1', _) -> leRel rel1' rel2
        (_, Just rel2') -> leRel rel1 rel2'
        -- TODO: Figure out if unification is enough at this stage
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
  (Relevance r1, Relevance r2) | r1 == r2 -> return ()
  _ -> throwError "unifyRel"

returnsType :: (Eq v, Hashable v, Show v)
            => Input s v -> TCM s v Bool
returnsType = go True
  where
    go reduce expr = case expr of
      Type   -> return True
      Lam {} -> return False
      Pi h _ t s  -> do
        x <- forallVar h (first meta t) r
        returnsType $ instantiate1 x s
      Case _ _ -> undefined -- TODO
      _ | reduce -> do
        expr' <- whnf metaRelevance toMetaAnnotation $ first meta expr
        go False $ first plicitness expr'
      _ -> return False
    meta = MetaAnnotation r . plicitness
    r = Relevance Relevant -- unimportant

makeRel :: (Eq v, Hashable v, Show v)
        => RelevanceM s -> Input s v -> TCM s v (Output s v)
makeRel rel expr = case expr of
  Var v -> return $ Var v
  Type -> return Type
  Pi h p t s -> do
    rType <- returnsType t
    if rType
    then Pi h (irrelMeta p) <$> makeRel (Relevance Irrelevant) t <*> makeRelScope h t s
    else Pi h (meta p) <$> makeRel rel t <*> makeRelScope h t s
  Lam h p t s -> Lam h (meta p) <$> makeRel rel t <*> makeRelScope h t s
  App e1 p e2 -> App <$> makeRel rel e1 <*> pure (meta p) <*> makeRel rel e2
  Case _ _ -> undefined -- TODO
  where
    irrelMeta = MetaAnnotation (Relevance Irrelevant) . plicitness
    meta = MetaAnnotation rel . plicitness
    makeRelScope h t s = do
      x <- forall_ h (first meta t) rel
      e <- makeRel rel $ instantiate1 (pure $ F x) s
      return $ abstract1 (F x) e

inferArg :: (Hashable v, Ord v, Show v)
         => Input s v -> Bool -> TCM s v (Output s v, RelevanceM s)
inferArg argType knownDef = do
  rType <- returnsType argType
  if rType
  then do
    argType' <- makeRel (Relevance Irrelevant) argType
    return (argType', Relevance Irrelevant)
  else do
    argType' <- check argType Type (Relevance Irrelevant) False
    if knownDef then do
      rel <- freshMetaRel
      return (argType', pure rel)
    else
      return (argType', Relevance Relevant)

inferTop :: (Hashable v, Ord v, Show v)
         => Input s v -> TCM s v (Output s v, RelevanceM s)
inferTop typ = do
  rType <- returnsType typ
  if rType
  then do
    typ' <- makeRel (Relevance Irrelevant) typ
    return (typ', Relevance Irrelevant)
  else do
    typ' <- check typ Type (Relevance Irrelevant) True
    return (typ', Relevance Relevant)

generalise :: Output s v -> Output s v -> TCM s v (Output s v, Output s v)
generalise e t = bitraverse (bitraverse f pure) (bitraverse f pure) (e, t)
  where
    f = fmap toMetaAnnotation . fromMetaAnnotation

infer :: (Hashable v, Ord v, Show v)
      => Input s v -> RelevanceM s -> Bool -> TCM s v (Output s v, Output s v)
infer expr surroundingRel knownDef = case expr of
  Var (F v) -> do
    leRel surroundingRel $ metaData v
    return (Var $ F v, metaType v)
  Var (B v)   -> do
    (_, t, a) <- context v
    leRel surroundingRel $ toRelevanceM a
    return (Var $ B v, bimap toMetaAnnotation B t)
  Type        -> return (Type, Type)
  Pi x p t1 s -> do
    (t1', t1rel) <- inferArg t1 knownDef
    v     <- forall_ x t1' t1rel
    e'    <- check (instantiate1 (pure $ F v) s) Type surroundingRel knownDef
    return ( Pi x (MetaAnnotation t1rel p) t1' $ abstract1 (F v) e'
           , Type
           )
  Lam x p t1 s -> uncurry generalise =<< do
    (t1', t1rel) <- inferArg t1 True
    v         <- forall_ x t1' t1rel
    (e', t2') <- infer (instantiate1 (pure $ F v) s) surroundingRel knownDef
    return ( Lam x (MetaAnnotation t1rel p) t1' $ abstract1 (F v) e'
           , Pi  x (MetaAnnotation t1rel p) t1' $ abstract1 (F v) t2'
           )
  App e1 p e2 -> do
    (e1', ft) <- infer e1 surroundingRel knownDef
    go True e1' ft
    where
      go reduce e1' ft = case ft of
        Pi _ rp@(MetaAnnotation rel p') argt s | plicitness p == p' -> do
          e2' <- check e2 argt rel knownDef
          return (App e1' rp e2', instantiate1 e2' s)
        _ | reduce -> do
          ft' <- whnf metaRelevance toMetaAnnotation ft
          go False e1' ft'
        _ -> throwError $ "infer relevance infer1" ++ show (pretty $ fmap show expr)
  _ -> throwError "infer relevance infer2"

check :: (Hashable v, Ord v, Show v)
      => Input s v -> Output s v -> RelevanceM s -> Bool -> TCM s v (Output s v)
check expr typ rel knownDef = do
  (expr', typ') <- infer expr rel knownDef
  subtype expr' typ' typ

subtype :: (Hashable v, Ord v, Show v)
        => Output s v -> Output s v -> Output s v -> TCM s v (Output s v)
subtype expr type1 type2 = go True expr type1 type2
  where
    go reduce e typ1 typ2 = case (typ1, typ2) of
      (Var (F v1), Var (F v2)) -> do
        leRel (metaData v2) (metaData v1)
        return e
      (Pi h1 (MetaAnnotation r1 p1) t1 s1,  Pi h2 (MetaAnnotation r2 p2) t2 s2) | p1 == p2 -> do
        x2 <- forall_ (h1 <> h2) t2 r1
        leRel r1 r2
        x1 <- go True (return $ F x2) t2 t1
        e2 <- go True (betaApp e (MetaAnnotation r1 p1) x1)
                      (instantiate1 x1 s1)
                      (instantiate1 (return $ F x2) s2)
        etaLamM sameMetaAnnotation
                (h1 <> h2)
                (MetaAnnotation r2 p2)
                t2
                (abstract1 (F x2) e2)
      _ | reduce -> do
        typ1' <- whnf metaRelevance toMetaAnnotation typ1
        typ2' <- whnf metaRelevance toMetaAnnotation typ2
        go False e typ1' typ2'
      _ -> do unify typ1 typ2; return e

sameMetaAnnotation :: MetaAnnotation s -> MetaAnnotation s -> TCM s v Bool
sameMetaAnnotation (MetaAnnotation r1 p1) (MetaAnnotation r2 p2)
  | p1 /= p2  = return False
  | otherwise = (==) <$> go r1 <*> go r2
  where
    go :: RelevanceM s -> TCM s v (RelevanceM s)
    go r@(Relevance _) = return r
    go r@(RVar v) = do
      sol <- liftST $ readSTRef $ metaRelRef v
      case sol of
        Nothing -> return r
        Just r' -> go r'

unify :: (Eq v, Hashable v, Show v) => Output s v -> Output s v -> TCM s v ()
unify type1 type2 = go True type1 type2
  where
    go reduce typ1 typ2
      | typ1 == typ2 = return ()
      | otherwise = case (typ1, typ2) of
        (Var (F v1), Var (F v2)) -> unifyRel (metaData v1) (metaData v2)
        (App t1 (MetaAnnotation r1 p1) t1', App t2 (MetaAnnotation r2 p2) t2') | p1 == p2 -> do
          unifyRel r1 r2
          go True t1 t2
          go True t2' t1'
        _ | reduce -> do
          typ1' <- whnf metaRelevance toMetaAnnotation typ1
          typ2' <- whnf metaRelevance toMetaAnnotation typ2
          go False typ1' typ2'
        _ -> throwError $ "rel unify: " ++ show (pretty (show <$> typ1, show <$> typ2))

checkRecursiveDefs :: (Hashable v, Ord v, Show v)
                   => Vector (InputScope s Int v, InputScope s Int v)
                   -> TCM s v (Vector (OutputScope s Int v, OutputScope s Int v, RelevanceM s))
checkRecursiveDefs ds = case traverse unusedScope $ snd <$> ds of
  Nothing -> throwError "Mutually recursive types not supported"
  Just ts -> do
    evs <- V.forM ts $ \t -> do
      (t', rel) <- inferTop t
      ev <- forall_ (Hint Nothing) t' rel
      return (ev, t', rel)
    let instantiatedDs = flip V.imap ds $ \i (s, _) ->
          (evs V.! i, instantiate (pure . pure . (\(ev, _, _) -> ev) . (evs V.!)) s)
    checkedDs <- V.forM instantiatedDs $ \((m, t, rel), e) -> do
      (e', t') <- infer e rel False
      e'' <- subtype e' t' t
      return (m, e'', t)
    V.forM checkedDs $ \(m, e, t) -> do
      let f  = unvar (const Nothing) $ flip V.elemIndex $ (\(ev, _, _) -> ev) <$> evs
          s  = abstract f e
          st = abstract f t
      return (s, st, metaData m)
