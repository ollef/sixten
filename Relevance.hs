{-# LANGUAGE Rank2Types #-}
module Relevance where

import Bound
import Bound.Var
import Control.Monad.Except
import Data.Hashable
import Data.Monoid
import Data.Function
import Data.Vector(Vector)
import qualified Data.Vector as V

import Annotation
import Core
import Monad
import Util

{-

All args to functions into type are irrelevant (indicated with '~'), e.g.
  ~(a : A) -> Type

All args of type Type or function into Type are irrelevant, e.g.
~(arg : Type)       -> B
~(arg : ~A -> Type) -> B

TODO
Args only used irrelevantly using the above rules are irrelevant, e.g. X in

forall ~{b : Type}~{X : b}{F : ~b -> Type}. F ~X -> F ~X

-}

data Meta s v = Meta
  { metaId   :: Int
  , metaRel  :: Relevance
  , metaType :: Output s v
  }

instance Eq (Meta s v) where
  x == y = compare x y == EQ

instance Ord (Meta s v) where
  compare = compare `on` metaId

freshExists :: Relevance -> Output s v -> TCM s v' (Meta s v)
freshExists r e = do
  i <- fresh
  return $ Meta i r e

type Input       s v   = Expr Plicitness (Var v (Meta s v))
type InputScope  s b v = Scope b (Expr Plicitness) (Var v (Meta s v))
type Output      s v   = Expr Annotation (Var v (Meta s v))
type OutputScope s b v = Scope b (Expr Annotation) (Var v (Meta s v))

checkArg :: (Hashable v, Ord v, Show v)
         => Input s v -> Output s v -> TCM s v (Output s v, Relevance)
checkArg expr typ = do
  (expr', typ', rel) <- inferArg expr
  expr'' <- subtype expr' typ' typ
  return (expr'', rel)

-- | If something has the type of the expression, then its relevance is...
inferArg :: (Hashable v, Ord v, Show v)
         => Input s v -> TCM s v (Output s v, Output s v, Relevance)
inferArg expr = case expr of
  Var (F v)   -> return (Var $ F v, metaType v, Relevant) -- TODO
  Var (B v)   -> do
    (_, t, a) <- context v
    return (Var $ B v, fmap B t, relevance a)
  Type        -> return (Type, Type, Irrelevant)
  Pi  x p t s -> do
    (t', trel) <- checkArg t Type
    v          <- freshExists trel t'
    (e', srel) <- checkArg (instantiate1 (return $ F v) s) Type
    return ( Pi x (Annotation trel p) t' $ abstract1 (F v) e'
           , Type
           , srel
           )
  Lam x p t1 s -> do
    (t1', t1rel)   <- checkArg t1 Type
    v              <- freshExists t1rel t1'
    (e', s', srel) <- inferArg (instantiate1 (return $ F v) s)
    return ( Lam x (Annotation t1rel p) t1' $ abstract1 (F v) e'
           , Pi  x (Annotation t1rel p) t1' $ abstract1 (F v) s'
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

check :: (Hashable v, Ord v, Show v)
      => Input s v -> Output s v -> Relevance -> TCM s v (Output s v)
check expr typ rel = do
  (expr', typ') <- infer expr rel
  subtype expr' typ' typ

subtype :: (Hashable v, Ord v)
        => Output s v -> Output s v -> Output s v -> TCM s v' (Output s v)
subtype expr typ1 typ2 = case (typ1, typ2) of
  _ | typ1 == typ2 -> return expr
  (Pi h1 rp1 t1 s1,  Pi h2 rp2 t2 s2) | plicitness rp1 == plicitness rp2 -> do
    x2 <- freshExists (relevance rp2) t2
    x1 <- subtype (return $ F x2) t2 t1
    expr2 <- subtype (betaApp expr rp1 x1)
                     (instantiate1 x1 s1)
                     (instantiate1 (return $ F x2) s2)
    return $ etaLam (h1 <> h2) rp2 t2 (abstract1 (F x2) expr2)
  _ -> error "relevance subtype"

infer :: (Hashable v, Ord v, Show v)
      => Input s v -> Relevance -> TCM s v (Output s v, Output s v)
infer expr surroundingRel = case expr of
  Var (F v)
    | surroundingRel <= metaRel v -> return (Var $ F v, metaType v)
    | otherwise                   -> throwError "irrelevant where relevant expected"
  Var (B v)   -> do
    (_, t, _) <- context v
    return (Var $ B v, fmap B t)
  Type        -> return (Type, Type)
  Lam x p t1 s -> do
    (t1', t1rel) <- checkArg t1 Type
    v            <- freshExists t1rel t1'
    (e', t2')    <- infer (instantiate1 (return $ F v) s) surroundingRel
    return ( Lam x (Annotation t1rel p) t1' $ abstract1 (F v) e'
           , Pi x  (Annotation t1rel p) t1' $ abstract1 (F v) t2'
           )
  App e1 p e2 -> do
    (e1', ft) <- infer e1 surroundingRel
    case ft of
      Pi _ rp argt s | plicitness p == plicitness rp -> do
        e2' <- check e2 argt (relevance rp)
        return (App e1' rp e2', instantiate1 e2' s)
      _ -> error "infer relevance infer"
  _ -> error "infer relevance infer"

checkTopLevel :: (Hashable v, Ord v, Show v)
              => Input s v -> Input s v
              -> TCM s v (Output s v, Output s v, Relevance)
checkTopLevel e t = do
  (t', rel) <- checkArg t Type
  e'        <- check e t' rel
  return (e', t', rel)

checkRecursiveDefs :: (Hashable v, Ord v, Show v)
                   => Vector (InputScope s Int v, InputScope s Int v)
                   -> TCM s v (Vector (OutputScope s Int v, OutputScope s Int v, Relevance))
checkRecursiveDefs ds = do
  case traverse unusedScope $ snd <$> ds of
    Nothing -> throwError "Mutually recursive types not supported"
    Just ts -> do
      evs <- V.forM ts $ \t -> do
        (t', rel) <- checkArg t Core.Type
        ev <- freshExists rel t'
        return (ev, t')
      let instantiatedDs = flip V.imap ds $ \i (s, _) ->
            (evs V.! i, instantiate (return . return . fst . (evs V.!)) s)
      checkedDs <- V.forM instantiatedDs $ \((m, t), e) -> do
        e' <- check e t $ metaRel m
        return (m, e', t)
      V.forM checkedDs $ \(m, e, t) -> do
        let f  = unvar (const Nothing) $ flip V.elemIndex $ fst <$> evs
            s  = abstract f e
            st = abstract f t
        return (s, st, metaRel m)



{-
checkRecursiveDefs :: (Ord v, Show v)
                   => Vector (NameHint, Scope Int Input.Expr (Var v (MetaVar s v)), Core s v)
                   -> TCM s v (Vector (NameHint, Scope Int (Core.Expr Plicitness) (Var v (MetaVar s v)), Core s v))
checkRecursiveDefs ds = do
  evs <- V.forM ds $ \(v, _, _) -> do
    tv <- freshExistsV mempty Core.Type
    freshForall v tv
  let instantiatedDs = flip V.map ds $ \(v, e, t) ->
        (v, instantiate (return . return . (evs V.!)) e, t)
  checkedDs <- V.forM instantiatedDs $ \(v, e, t) -> do
    (e', t') <- checkType e t
    return (v, e', t')
  V.forM checkedDs $ \(v, e, t) -> do
    (ge, gt) <- generalise e t
    s <- abstractM (flip V.elemIndex evs) ge
    return (v, s, gt)
    -}
