{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, RecursiveDo #-}
module Relevance where

import Control.Monad.Except
import Control.Monad.ST.Class
import Data.Bifunctor
import Data.Bitraversable
import Data.Monoid
import Data.STRef
import Data.Function
import Data.Vector(Vector)
import qualified Data.Vector as V

import qualified Builtin
import Meta
import Monad
import Normalise
import Syntax
import Syntax.Abstract
import Syntax.Annotation as Annotation
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

freshMetaRel :: TCM s (MetaRel s)
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

fromMetaAnnotation :: MetaAnnotation s -> TCM s Annotation
fromMetaAnnotation (MetaAnnotation r p) = Annotation <$> fromRelevanceM r <*> pure p

fromRelevanceM :: RelevanceM s -> TCM s Annotation.Relevance
fromRelevanceM (Relevance r) = return r
fromRelevanceM (RVar v) = do
  sol <- liftST $ readSTRef $ metaRelRef v
  case sol of
    Nothing -> return Annotation.Irrelevant
    Just r' -> fromRelevanceM r'

type Input       s = Expr Plicitness (MetaVar s (RelevanceM s) (MetaAnnotation s))
type InputScope  s b = Scope b (Expr Plicitness) (MetaVar s (RelevanceM s) (MetaAnnotation s))
type Output      s = AbstractM s (RelevanceM s) (MetaAnnotation s)
type OutputScope s b = ScopeM b (Expr (MetaAnnotation s)) s (RelevanceM s) (MetaAnnotation s)

leRel :: RelevanceM s -> RelevanceM s -> TCM s ()
leRel rel1 rel2 = do
  trs "leRel rel1" rel1
  trs "leRel rel2" rel2
  case (rel1, rel2) of
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

unifyRel :: RelevanceM s -> RelevanceM s -> TCM s ()
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

returnsType :: Input s -> TCM s Bool
returnsType = go True
  where
    go reduce expr = case expr of
      Type   -> return True
      Lam {} -> return False
      Con _  -> return False
      Lit _  -> return False
      Pi h _ t s  -> do
        x <- forallVar h (first meta t) r
        returnsType $ instantiate (pure x) s
      Case _ brs -> branchesReturnType brs
      _ | reduce -> do
        expr' <- whnf metaRelevance toMetaAnnotation $ first meta expr
        go False $ first plicitness expr'
      _ -> return False
    meta = MetaAnnotation r . plicitness
    r = Relevance Relevant -- unimportant
    branchesReturnType (ConBranches cbrs) = and <$> sequence
      [do vs <- forTele tele $ \h _ _ -> forallVar h Type r
          returnsType $ instantiateTele vs s
      | (_, tele, s) <- cbrs]
    branchesReturnType (LitBranches lbrs def) = and <$> sequence
      (returnsType def : [returnsType e | (_, e) <- lbrs])

makeRel :: RelevanceM s -> Input s -> TCM s (Output s)
makeRel rel expr = do
  tr "makeRel expr" expr
  trs "makeRel  rel" rel
  modifyIndent succ
  res <- case expr of
    Var v -> return $ Var v
    Global g -> return $ Global g
    Con c -> return $ Con c
    Lit l -> return $ Lit l
    Type -> return Type
    Pi h p t s -> do
      rType <- returnsType t
      if rType
      then Pi h (irrelMeta p) <$> makeRel (Relevance Irrelevant) t <*> makeRelScope h t s
      else Pi h (meta p) <$> makeRel rel t <*> makeRelScope h t s
    Lam h p t s -> Lam h (meta p) <$> makeRel rel t <*> makeRelScope h t s
    App e1 p e2 -> App <$> makeRel rel e1 <*> pure (meta p) <*> makeRel rel e2
    Case e brs -> Case <$> makeRel rel e <*> makeRelBranches brs
  modifyIndent pred
  tr "makeRel res" res
  return res
  where
    irrelMeta = MetaAnnotation (Relevance Irrelevant) . plicitness
    meta = MetaAnnotation rel . plicitness
    makeRelScope h t s = do
      x <- forall_ h (first meta t) rel
      e <- makeRel rel $ instantiate1 (pure x) s
      return $ abstract1 x e
    makeRelBranches (ConBranches cbrs)     = ConBranches
      <$> sequence [ mdo
        vs <- forTele tele $ \h p s -> do
          let t = inst s
          -- TODO should this be obtained from the type instead?
          rType <- returnsType t
          t' <- if rType then makeRel (Relevance Irrelevant) t
                         else makeRel rel t
          v <- forall_ h t' rel
          return (v, (h, (if rType then irrelMeta else meta) p, abstr t'))
        let inst = instantiateTele (pure . fst <$> vs)
            abstr = abstract $ teleAbstraction (fst <$> vs)
            tele' = snd <$> vs
        bre <- makeRel rel (inst brs)
        return (c, Telescope tele', abstr bre)
                   | (c, tele, brs) <- cbrs ]
    makeRelBranches (LitBranches lbrs def) = LitBranches
      <$> sequence [(,) l <$> makeRel rel e | (l, e) <- lbrs] <*> makeRel rel def

inferArg :: Input s -> Bool -> TCM s (Output s, RelevanceM s)
inferArg argType knownDef = do
  tr  "inferArg argType " argType
  trs "inferArg knownDef" knownDef
  modifyIndent succ
  rType <- returnsType argType
  (res, rel) <- if rType
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
  modifyIndent pred
  tr  "inferArg res" res
  trs "inferArg rel" rel
  return (res, rel)

inferTop :: Input s -> TCM s (Output s, RelevanceM s)
inferTop typ = do
  tr "inferTop typ" typ
  modifyIndent succ
  rType <- returnsType typ
  (typ', rel) <- if rType
    then do
      typ' <- makeRel (Relevance Irrelevant) typ
      return (typ', Relevance Irrelevant)
    else do
      typ' <- check typ Type (Relevance Irrelevant) True
      return (typ', Relevance Relevant)
  modifyIndent pred
  tr "inferTop res" typ'
  trs "inferTop rel" rel
  return (typ', rel)

generalise :: Output s -> Output s -> TCM s (Output s, Output s)
generalise e t = bitraverse (bitraverse f pure) (bitraverse f pure) (e, t)
  where
    f = fmap toMetaAnnotation . fromMetaAnnotation

infer :: Input s -> RelevanceM s -> Bool -> TCM s (Output s, Output s)
infer expr surroundingRel knownDef = do
  tr "infer expr" expr
  trs "infer srel" surroundingRel
  trs "infer know" knownDef
  modifyIndent succ
  (expr', typ) <- case expr of
    Var v -> do
      leRel surroundingRel $ metaData v
      return (Var v, metaType v)
    Global v -> do
      (_, t, a) <- context v
      leRel surroundingRel $ toRelevanceM a
      return (Global v, first toMetaAnnotation t)
    Con c -> do
      t <- qconstructor c
      return (Con c, first toMetaAnnotation t)
    Lit l -> return (Lit l, Builtin.int)
    Type        -> return (Type, Type)
    Pi x p t1 s -> do
      (t1', t1rel) <- inferArg t1 knownDef
      v     <- forall_ x t1' t1rel
      e'    <- check (instantiate1 (pure v) s) Type surroundingRel knownDef
      return ( Pi x (MetaAnnotation t1rel p) t1' $ abstract1 v e'
             , Type
             )
    Lam x p t1 s -> uncurry generalise =<< do
      (t1', t1rel) <- inferArg t1 True
      v         <- forall_ x t1' t1rel
      (e', t2') <- infer (instantiate1 (pure v) s) surroundingRel knownDef
      return ( Lam x (MetaAnnotation t1rel p) t1' $ abstract1 v e'
             , Pi  x (MetaAnnotation t1rel p) t1' $ abstract1 v t2'
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
    Case e brs -> do
      (e', _) <- infer e surroundingRel knownDef
      (brs', retType) <- inferBranches brs surroundingRel knownDef
      return (Case e' brs', retType)
  modifyIndent pred
  tr "infer res e" expr'
  tr "infer res t" typ
  return (expr', typ)

inferBranches :: Branches Plicitness (Expr Plicitness) (MetaVar s (RelevanceM s) (MetaAnnotation s))
              -> RelevanceM s
              -> Bool
              -> TCM s (Branches (MetaAnnotation s) (Expr (MetaAnnotation s)) (MetaVar s (RelevanceM s) (MetaAnnotation s)), Output s)
inferBranches (ConBranches cbrs) surroundingRel knownDef = do
  cbrs' <- forM cbrs $ \(c, tele, sbr) -> mdo
    ps <- forTele tele $ \h p s -> do
      let t = inst s
      (t', t'rel) <- inferArg t True
      v <- forall_ h t' t'rel
      return (v, h, MetaAnnotation t'rel p, abstr t')
    let inst  = instantiateTele $ (\(v, _, _, _) -> pure v) <$> ps
        abstr = abstract $ teleAbstraction $ (\(v, _, _, _) -> v) <$> ps
    let tele' = Telescope $ (\(_, h, p, s) -> (h, p, s)) <$> ps
    (sbr', brType) <- infer (inst sbr) surroundingRel knownDef
    return (c, tele', sbr', brType, abstr)
  let retType = case cbrs' of
        ((_, _, _, t, _):_) -> t
        _ -> undefined
  cbrs'' <- forM cbrs' $ \(c, tele, sbr, brType, abstr) -> do
    sbr' <- subtype sbr brType retType
    return (c, tele, abstr sbr')
  return (ConBranches cbrs'', retType)

inferBranches (LitBranches lbrs def) surroundingRel knownDef = undefined

check :: Input s -> Output s -> RelevanceM s -> Bool -> TCM s (Output s)
check expr typ rel knownDef = do
  tr "check e" expr
  tr "check t" typ
  trs "check r" rel
  trs "check k" knownDef
  modifyIndent succ
  (expr', typ') <- infer expr rel knownDef
  res <- subtype expr' typ' typ
  modifyIndent pred
  tr "check res" res
  return res

subtype :: Output s -> Output s -> Output s -> TCM s (Output s)
subtype expr type1 type2 = do
  tr "subtype e " expr
  tr "subtype t1" type1
  tr "subtype t2" type2
  modifyIndent succ
  e' <- go True expr type1 type2
  modifyIndent pred
  tr "subtype res" e'
  return e'
  where
    go reduce e typ1 typ2 = case (typ1, typ2) of
      (Var v1, Var v2) -> do
        leRel (metaData v2) (metaData v1)
        return e
      (Pi h1 (MetaAnnotation r1 p1) t1 s1,  Pi h2 (MetaAnnotation r2 p2) t2 s2) | p1 == p2 -> do
        x2 <- forall_ (h1 <> h2) t2 r1
        leRel r1 r2
        x1 <- subtype (pure x2) t2 t1
        e2 <- subtype (betaApp e (MetaAnnotation r1 p1) x1)
                      (instantiate1 x1 s1)
                      (instantiate1 (pure x2) s2)
        etaLamM sameMetaAnnotation
                (h1 <> h2)
                (MetaAnnotation r2 p2)
                t2
                (abstract1 x2 e2)
      _ | reduce -> do
        typ1' <- whnf metaRelevance toMetaAnnotation typ1
        typ2' <- whnf metaRelevance toMetaAnnotation typ2
        go False e typ1' typ2'
      _ -> do unify typ1 typ2; return e

sameMetaAnnotation :: MetaAnnotation s -> MetaAnnotation s -> TCM s Bool
sameMetaAnnotation (MetaAnnotation r1 p1) (MetaAnnotation r2 p2)
  | p1 /= p2  = return False
  | otherwise = (==) <$> go r1 <*> go r2
  where
    go :: RelevanceM s -> TCM s (RelevanceM s)
    go r@(Relevance _) = return r
    go r@(RVar v) = do
      sol <- liftST $ readSTRef $ metaRelRef v
      case sol of
        Nothing -> return r
        Just r' -> go r'

unify :: Output s -> Output s -> TCM s ()
unify type1 type2 = do
  tr "unify t1" type1
  tr "unify t2" type2
  modifyIndent succ
  go True type1 type2
  modifyIndent pred
  where
    go reduce typ1 typ2
      | typ1 == typ2 = return ()
      | otherwise = case (typ1, typ2) of
        (Var v1, Var v2) -> unifyRel (metaData v1) (metaData v2)
        (App t1 (MetaAnnotation r1 p1) t1', App t2 (MetaAnnotation r2 p2) t2') | p1 == p2 -> do
          unifyRel r1 r2
          unify t1 t2
          unify t2' t1'
        _ | reduce -> do
          typ1' <- whnf metaRelevance toMetaAnnotation typ1
          typ2' <- whnf metaRelevance toMetaAnnotation typ2
          go False typ1' typ2'
        _ -> throwError $ "rel unify: " ++ show (pretty (show <$> typ1, show <$> typ2))

inferConstr :: ConstrDef (Input s) -> TCM s (ConstrDef (Output s))
inferConstr (ConstrDef c t) = do
  trs "inferConstr" c
  modifyIndent succ
  res <- ConstrDef c <$> check t Type (Relevance Irrelevant) False
  modifyIndent pred
  return res

inferDef :: Definition Plicitness (Expr Plicitness) (MetaVar s (RelevanceM s) (MetaAnnotation s))
         -> RelevanceM s
         -> TCM s (Definition (MetaAnnotation s) (Expr (MetaAnnotation s))
                              (MetaVar s (RelevanceM s) (MetaAnnotation s)), Output s)
inferDef (Definition e) surroundingRel = first Definition <$> infer e surroundingRel False
inferDef (DataDefinition (DataDef ps cs)) _surroundingRel = mdo
  trs "inferDef" ()
  modifyIndent succ
  let inst = instantiateTele $ (\(v, _, _, _) -> pure v) <$> ps'
  ps' <- forTele ps $ \h p s -> do
    let t = inst s
    rType <- returnsType t
    let rel = Relevance $ if rType then Irrelevant else Relevant
    t' <- makeRel rel t
    v <- forall_ h t' rel
    return (v, h, MetaAnnotation rel p, t')
  let abstr = abstract $ teleAbstraction $ (\(v, _, _, _) -> v) <$> ps'
      ps'' = (\(_, h, p, t) -> (h, p, abstr t)) <$> ps'
  cs' <- mapM inferConstr $ fmap (fmap inst) cs
  let cs'' = fmap abstr <$> cs'
      res = DataDef (Telescope ps'') cs''
      resType = dataType res Pi (Scope Type)
  modifyIndent pred
  return (DataDefinition res, resType)

subtypeDef :: Definition (MetaAnnotation s) (Expr (MetaAnnotation s))
                           (MetaVar s (RelevanceM s) (MetaAnnotation s))
           -> Output s
           -> Output s
           -> TCM s (Definition (MetaAnnotation s) (Expr (MetaAnnotation s))
                                  (MetaVar s (RelevanceM s) (MetaAnnotation s)))
subtypeDef (Definition e) t t' = Definition <$> subtype e t t'
subtypeDef (DataDefinition d) t t' = do
  unify t t'
  return $ DataDefinition d

checkRecursiveDefs :: Vector (Definition Plicitness (Expr Plicitness) (Var Int (MetaVar s (RelevanceM s) (MetaAnnotation s))), InputScope s Int)
                   -> TCM s (Vector (Definition (MetaAnnotation s) (Expr (MetaAnnotation s)) (Var Int (MetaVar s (RelevanceM s) (MetaAnnotation s))), OutputScope s Int, RelevanceM s))
checkRecursiveDefs ds = case traverse unusedScope $ snd <$> ds of
  Nothing -> throwError "Mutually recursive types not supported"
  Just ts -> do
    evs <- V.forM ts $ \t -> do
      (t', rel) <- inferTop t
      ev <- forall_ (Hint Nothing) t' rel
      return (ev, t', rel)
    let instantiatedDs = flip V.imap ds $ \i (d, _) ->
          (evs V.! i, instantiateDef (pure . (\(ev, _, _) -> ev) . (evs V.!)) d)
    checkedDs <- V.forM instantiatedDs $ \((m, t, rel), d) -> do
      (d', t') <- inferDef d rel
      d'' <- subtypeDef d' t' t
      return (m, d'', t)
    V.forM checkedDs $ \(m, d, t) -> do
      let f  = flip V.elemIndex $ (\(ev, _, _) -> ev) <$> evs
          s  = abstractDef f d
          st = abstract f t
      return (s, st, metaData m)
