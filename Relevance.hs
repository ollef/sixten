{-# LANGUAGE Rank2Types #-}
module Relevance where

import Bound
import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.ST.Class
import Data.Monoid
import Data.STRef
import Data.Function

import Core
import Util

{-

All args to functions into type are made irrelevant, e.g.
  !(a : A) -> Type

All args of type Type or function into Type are made irrelevant, e.g.
!(arg : Type)       -> B
!(arg : !A -> Type) -> B

Args only used irrelevantly using the above rules should be irrelevant, e.g. X
in

forall !{b : Type}!{X : b}{F : !b -> Type}. F !X -> F !X

-}

data Decoration = Decoration Relevance Plicitness
  deriving (Eq, Ord, Show)

instance HasRelevance Decoration where
  relevance (Decoration r _) = r

instance HasPlicitness Decoration where
  plicitness (Decoration _ p) = p

type RIM s a = ReaderT (STRef s Int) (ST s) a

runRIM :: (forall s. RIM s a) -> a
runRIM f = runST $ runReaderT f =<< newSTRef 0

data Meta s = Meta
  { metaId   :: Int
  , metaRel  :: STRef s Relevance
  , metaType :: Output s
  } deriving Eq

instance Ord (Meta s) where
  compare = compare `on` metaId

newMeta :: Relevance -> Output s -> RIM s (Meta s)
newMeta r e = do
  rid <- ask
  rr <- liftST $ newSTRef r
  i  <- liftST $ readSTRef rid
  liftST $ writeSTRef rid $! i + 1
  return $ Meta i rr e

type Input  s = Expr Plicitness (Meta s)
type Output s = Expr Decoration (Meta s)

checkArg :: Input s -> Output s -> RIM s (Output s, Relevance)
checkArg expr typ = do
  (expr', typ', rel) <- inferArg expr
  expr'' <- subtype expr' typ' typ
  return (expr'', rel)

inferArg :: Input s -> RIM s (Output s, Output s, Relevance)
inferArg expr = case expr of
  Var v       ->
    -- rel <- liftST $ readSTRef $ metaRel v
    return (Var v, metaType v, Relevant)
  Type        -> return (Type, Type, Irrelevant)
  Pi  x p t s -> do
    (t', trel) <- checkArg t Type
    v  <- newMeta trel t'
    (e', srel) <- checkArg (instantiate1 (return v) s) Type
    vrel <- liftST $ readSTRef (metaRel v)
    return (Pi x (Decoration (leastRelevant srel vrel) p) t' $ abstract1 v e', Type, srel)
  Lam x p t1 s -> do
    (t1', t1rel) <- checkArg t1 Type
    v   <- newMeta t1rel t1'
    (e', s', srel) <- inferArg (instantiate1 (return v) s)
    vrel <- liftST $ readSTRef (metaRel v)
    return ( Lam x (Decoration vrel p) t1' $ abstract1 v e'
           , Pi  x (Decoration vrel p) t1' $ abstract1 v s'
           , srel
           )
  App e1 p e2 -> do
    (e1', ft, e1rel) <- inferArg e1
    case ft of
      Pi _ rp argt s | plicitness p == plicitness rp -> do
        e2' <- check e2 argt (relevance rp)
        return (App e1' rp e2', instantiate1 e2' s, e1rel)
      _ -> error "infer relevance infer"
  _ -> error "infer relevance type"

check :: Input s -> Output s -> Relevance -> RIM s (Output s)
check expr typ rel = do
  (expr', typ') <- infer expr rel
  subtype expr' typ' typ

subtype :: Output s -> Output s -> Output s -> RIM s (Output s)
subtype expr typ1 typ2 = case (typ1, typ2) of
  _ | typ1 == typ2 -> return expr
  (Pi h1 rp1 t1 s1,  Pi h2 rp2 t2 s2) | plicitness rp1 == plicitness rp2 -> do
    x2 <- newMeta (relevance rp2) t2
    x1 <- subtype (return x2) t2 t1
    expr2 <- subtype (betaApp expr rp1 x1)
                     (instantiate1 x1 s1)
                     (instantiate1 (return x2) s2)
    return $ etaLam (h1 <> h2) rp2 t2 (abstract1 x2 expr2)
  _ -> error "relevance subtype"

infer :: Input s -> Relevance -> RIM s (Output s, Output s)
infer expr surroundingRel = case expr of
  Var v       -> do
    lift $ modifySTRef' (metaRel v) (mostRelevant surroundingRel)
    return (Var v, metaType v)
  Type        -> return (Type, Type)
  Lam x p t1 s -> do
    (t1', _t1rel) <- checkArg t1 Type
    v            <- newMeta Irrelevant t1'
    (e', t2')    <- infer (instantiate1 (return v) s) surroundingRel
    rel <- liftST $ readSTRef (metaRel v)
    return ( Lam x (Decoration rel p) t1' $ abstract1 v e'
           , Pi x (Decoration rel p) t1' $ abstract1 v t2'
           )
  App e1 p e2 -> do
    (e1', ft) <- infer e1 surroundingRel
    case ft of
      Pi _ rp argt s | plicitness p == plicitness rp -> do
        e2' <- check e2 argt (relevance rp)
        return (App e1' rp e2', instantiate1 e2' s)
      _ -> error "infer relevance infer"
  _ -> error "infer relevance infer"

test :: Expr Plicitness Empty -> Type Plicitness Empty -> (Expr Decoration a, Type Decoration a)
test e _t = runRIM $ do
  -- (t', _, _) <- inferArg (fmap fromEmpty t)
  -- e'         <- check (fmap fromEmpty e) t' Relevant
  (e', t') <- infer (fmap fromEmpty e) Relevant
  return (fmap (error "infer relevance test") e', fmap (error "infer relevance test") t')
