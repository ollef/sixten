module Inference.Subtype where

import Control.Monad
import Data.Bifunctor
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import {-# SOURCE #-} Inference.Class
import Analysis.Simplify
import Inference.Monad
import Inference.Unify
import Meta
import Syntax
import Syntax.Abstract as Abstract
import Util
import Util.Tsil
import VIX

--------------------------------------------------------------------------------
-- Prenex conversion/deep skolemisation
-- | prenexConvert t1 = (t2, f) => f : t2 -> t1
prenexConvert
  :: Polytype
  -> Infer (Rhotype, AbstractM -> Infer AbstractM)
prenexConvert t1 = do
  (vs, t2, f) <- prenexConvertInner t1
  return
    ( t2
    , \x ->
      f =<< Abstract.lams
        <$> metaTelescopeM vs
        <*> abstractM (teleAbstraction $ snd <$> vs) x
    )

prenexConvertInner
  :: Polytype
  -> Infer (Vector (Plicitness, MetaA), Rhotype, AbstractM -> Infer AbstractM)
prenexConvertInner typ = do
  typ' <- whnf typ
  prenexConvertInner' typ'

prenexConvertInner'
  :: Polytype
  -> Infer (Vector (Plicitness, MetaA), Rhotype, AbstractM -> Infer AbstractM)
prenexConvertInner' (Pi h p t resScope) = do
  y <- forall h p t
  let resType = Util.instantiate1 (pure y) resScope
  (vs, resType', f) <- prenexConvertInner resType
  let implicitCase =
        ( Vector.cons (p, y) vs
        , resType'
        , \x -> fmap (Lam h p t) $ abstract1M y
          =<< f (betaApp x p $ pure y)
        )
  return $ case p of
    Constraint -> implicitCase
    Implicit -> implicitCase
    Explicit ->
      ( vs
      , Pi h p t $ abstract1 y resType'
      , \x -> fmap (Lam h p t) . abstract1M y
        =<< f
        =<< lams <$> metaTelescopeM vs
        <*> abstractM (teleAbstraction $ snd <$> vs)
        (betaApp (betaApps x $ second pure <$> vs) p $ pure y)
      )
prenexConvertInner' typ = return (mempty, typ, pure)

-- | skolemise t1 = (t2, f) => f : t2 -> t1
--
-- Peel off quantifiers from the given type, instantiating them with skolem
-- variables ('forall'), and return a function that takes a term of the peeled
-- type and produces a term of the unpeeled type.
skolemise
  :: Polytype
  -> InstUntil
  -> Infer (Rhotype, AbstractM -> Infer AbstractM)
skolemise typ instUntil = do
  typ' <- whnf typ
  skolemise' typ' instUntil

skolemise'
  :: Polytype
  -> InstUntil
  -> Infer (Rhotype, AbstractM -> Infer AbstractM)
skolemise' (Pi h p t resScope) instUntil
  | shouldInst p instUntil = do
    v <- forall h p t
    let resType = Util.instantiate1 (pure v) resScope
    (resType', f) <- skolemise resType instUntil
    return
      ( resType'
      , \x -> fmap (Lam h p t) $ abstract1M v
        =<< f x
      )
skolemise' typ _ = return (typ, pure)

--------------------------------------------------------------------------------
-- Subtyping/subsumption
-- | subtype t1 t2 = f => f : t1 -> t2
subtype :: Polytype -> Polytype -> Infer (AbstractM -> Infer AbstractM)
subtype typ1 typ2 = do
  logMeta 30 "subtype t1" typ1
  logMeta 30 "        t2" typ2
  modifyIndent succ
  typ1' <- whnf typ1
  typ2' <- whnf typ2
  res <- subtype' typ1' typ2'
  modifyIndent pred
  return res

subtype' :: Polytype -> Polytype -> Infer (AbstractM -> Infer AbstractM)
subtype' (Pi h1 p1 argType1 retScope1) (Pi h2 p2 argType2 retScope2)
  | p1 == p2 = do
    let h = h1 <> h2
    f1 <- subtype argType2 argType1
    v2 <- forall h p1 argType2
    v1 <- f1 $ pure v2
    let retType1 = Util.instantiate1 v1 retScope1
        retType2 = Util.instantiate1 (pure v2) retScope2
    f2 <- subtype retType1 retType2
    return
      $ \x -> fmap (Lam h p2 argType2)
      $ abstract1M v2 =<< f2 (App x p1 v1)
subtype' typ1 typ2 = do
  (rho, f1) <- skolemise typ2 $ InstUntil Explicit
  f2 <- subtypeRho typ1 rho $ InstUntil Explicit
  return $ f1 <=< f2

subtypeRho :: Polytype -> Rhotype -> InstUntil -> Infer (AbstractM -> Infer AbstractM)
subtypeRho typ1 typ2 instUntil = do
  logMeta 30 "subtypeRho t1" typ1
  logMeta 30 "           t2" typ2
  modifyIndent succ
  typ1' <- whnf typ1
  typ2' <- whnf typ2
  res <- subtypeRho' typ1' typ2' instUntil
  modifyIndent pred
  return res

subtypeRho' :: Polytype -> Rhotype -> InstUntil -> Infer (AbstractM -> Infer AbstractM)
subtypeRho' typ1 typ2 _ | typ1 == typ2 = return pure
subtypeRho' (Pi h1 p1 argType1 retScope1) (Pi h2 p2 argType2 retScope2) _
  | p1 == p2 = do
    let h = h1 <> h2
    f1 <- subtype argType2 argType1
    v2 <- forall h p1 argType2
    v1 <- f1 $ pure v2
    let retType1 = Util.instantiate1 v1 retScope1
        retType2 = Util.instantiate1 (pure v2) retScope2
    f2 <- subtypeRho retType1 retType2 $ InstUntil Explicit
    return
      $ \x -> fmap (Lam h p2 argType2)
      $ abstract1M v2 =<< f2 (App x p1 v1)
subtypeRho' (Pi h p t s) typ2 instUntil | shouldInst p instUntil = do
  v <- existsVar h p t
  f <- subtypeRho (Util.instantiate1 v s) typ2 instUntil
  return $ \x -> f $ App x p v
subtypeRho' typ1 typ2 _ = do
  unify [] typ1 typ2
  return pure

-- | funSubtypes typ ps = (ts, retType, f) => f : (ts -> retType) -> typ
funSubtypes
  :: Rhotype
  -> Vector Plicitness
  -> Infer
    ( Telescope Plicitness Expr MetaA
    , Scope TeleVar Expr MetaA
    , Vector (AbstractM -> Infer AbstractM)
    )
funSubtypes startType plics = go plics startType mempty mempty mempty
  where
    go ps typ vs tele fs
      | Vector.null ps = do
        let vars = toVector vs
            funs = toVector fs
            abstr = teleAbstraction vars
        tele' <- forM (toVector tele) $ \(h, p, t) -> do
          s <- abstractM abstr t
          return $ TeleArg h p s

        typeScope <- abstractM abstr typ

        return (Telescope tele', typeScope, funs)
      | otherwise = do
        let p = Vector.head ps
        (h, argType, resScope, f) <- funSubtype typ p
        v <- forall mempty p argType
        go
          (Vector.tail ps)
          (Util.instantiate1 (pure v) resScope)
          (Snoc vs v)
          (Snoc tele (h, p, argType))
          (Snoc fs f)

-- | funSubtype typ p = (typ1, typ2, f) => f : (typ1 -> typ2) -> typ
funSubtype
  :: Rhotype
  -> Plicitness
  -> Infer (NameHint, Rhotype, Scope1 Expr MetaA, AbstractM -> Infer AbstractM)
funSubtype typ p = do
  typ' <- whnf typ
  funSubtype' typ' p

funSubtype'
  :: Rhotype
  -> Plicitness
  -> Infer (NameHint, Rhotype, Scope1 Expr MetaA, AbstractM -> Infer AbstractM)
funSubtype' (Pi h p t s) p' | p == p' = return (h, t, s, pure)
funSubtype' typ p = do
  argType <- existsType mempty
  resType <- existsType mempty
  let resScope = abstractNone resType
  f <- subtypeRho' (Pi mempty p argType resScope) typ $ InstUntil p
  return (mempty, argType, resScope, f)

-- | subtypeFun typ p = (typ1, typ2, f) => f : typ -> (typ1 -> typ2)
subtypeFun
  :: Rhotype
  -> Plicitness
  -> Infer (Rhotype, Scope1 Expr MetaA, AbstractM -> Infer AbstractM)
subtypeFun typ p = do
  typ' <- whnf typ
  subtypeFun' typ' p

subtypeFun'
  :: Rhotype
  -> Plicitness
  -> Infer (Rhotype, Scope1 Expr MetaA, AbstractM -> Infer AbstractM)
subtypeFun' (Pi _ p t s) p' | p == p' = return (t, s, pure)
subtypeFun' typ p = do
  argType <- existsType mempty
  resType <- existsType mempty
  let resScope = abstractNone resType
  f <- subtype typ $ Pi mempty p argType resScope
  return (argType, resScope, f)
