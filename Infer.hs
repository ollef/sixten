{-# LANGUAGE ViewPatterns #-}
module Infer where

import Bound
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.ST()
import Control.Monad.ST.Class
import Data.Bifunctor
import Data.Bitraversable
import Data.Either
import Data.Foldable as F
import Data.Function
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import qualified Data.Set as S
import Data.STRef
import Data.Traversable as T
import Text.Trifecta.Result

import qualified Core
import qualified Input
import Monad
import qualified Parser
import Pretty
import TopoSort
import Util

showMeta :: (Functor f, Foldable f, Pretty (f String)) => f (MetaVar s) -> TCM s Doc
showMeta x = do
  vs <- nub <$> foldMapM (:[]) x
  let p (metaRef -> Just r) = either (const Nothing) Just <$> solution r
      p _                   = return Nothing
  pvs <- T.mapM p vs
  let sv v = "[" ++ (if isJust $ metaRef v then "∃" else "") ++ show (metaId v) ++ ":" ++ show (pretty $ sv <$> metaType v) ++ "]"
  let solutions = [(sv v, pretty $ fmap sv <$> msol) | (v, msol) <- zip vs pvs]
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

whnf :: Core s -> TCM s (Core s)
whnf expr = case expr of
  Core.Var (metaRef -> Nothing) -> return expr
  Core.Var (metaRef -> Just r)  -> refine r expr whnf
  Core.Var _                    -> throwError "whnf impossible"
  Core.Type                     -> return expr
  Core.Pi {}                    -> return expr
  Core.Lam {}                   -> return expr
  Core.App e1 p e2              -> do
    e1' <- whnf e1
    case e1' of
      Core.Lam h p' t2 s | p == p' -> do
        e2' <- freshLetV h e2 t2
        whnf $ instantiate1 e2' s
      _ -> return expr
  Core.Case _ _ -> undefined -- TODO

normalise :: Core s -> TCM s (Core s)
normalise expr = case expr of
  Core.Var (metaRef -> Nothing) -> return expr
  Core.Var (metaRef -> Just r)  -> refine r expr normalise
  Core.Var _                    -> throwError "normalise impossible"
  Core.Type                     -> return expr
  Core.Pi n p a s               -> normaliseScope n (Core.Pi n p)  a s
  Core.Lam n p a s              -> normaliseScope n (Core.Lam n p) a s
  Core.App e1 p e2              -> do
    e1' <- normalise e1
    e2' <- normalise e2
    case e1' of
      Core.Lam _ p' _ s | p == p' -> normalise $ instantiate1 e2' s
      _                           -> return $ Core.App e1' p e2'
  Core.Case _ _ -> undefined -- TODO
  where
    normaliseScope h c a s = do
      x <- freshForall h a
      ns <- normalise $ instantiate1 (return x) s
      c a <$> abstract1M x ns

inferPi :: Input s -> Plicitness
        -> TCM s (Core s, Core s, Scope1 Core.Expr (MetaVar s))
inferPi expr p = do
  tr "inferPi" expr
  modifyIndent succ
  (e, t) <- inferType expr
  (a, b, c) <- go True e t
  modifyIndent pred
  tr "inferPi res a" a
  tr "            b" b
  cv <- freshForallV mempty Core.Type
  tr "            c" $ instantiate1 cv c
  return (a, b, c)
  where
    go reduce e t = case t of
      Core.Pi _ p' vt s | p == p' -> return (e, vt, s)
      Core.Pi h Implicit vt s     -> do
        v <- freshExistsV h vt
        go True (Core.betaApp e Implicit v) (instantiate1 v s)
      Core.Var v@(metaRef -> Just r) -> do
        sol <- solution r
        unify (metaType v) Core.Type
        case sol of
          Left l -> do
            t1 <- freshExistsLV (metaHint v) Core.Type l
            t2 <- freshExistsLV (metaHint v) Core.Type l
            let at2 = abstractNothing t2
            solve r $ Core.Pi mempty p t1 at2
            return (e, t1, at2)
          Right c -> go True e c
      _ | reduce                  -> go False e =<< whnf t
      _                           -> do
        s <- showMeta t
        throwError $ "Expected function, got " ++ show s

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

{-
instantiate1M :: Scope1 Core.Expr (MetaVar s) -> Core s -> TCM s (Core s)
instantiate1M s e = do
  changed <- liftST $ newSTRef False
  join <$> traverse (go changed) (fromScope s)
  where
    go changed (B ()) = do
      liftST $ writeSTRef changed True
      return e
    go changed (F v@(metaRef -> Just r)) = do
      sol <- solution r
      case sol of
        Left _  -> return $ return v
        Right c -> do
          changed' <- liftST $ newSTRef False
          c' <- traverse (go changed') c
          hasChanged <- liftST $ readSTRef changed'
          if hasChanged then do
            liftST $ writeSTRef changed True
            return c'
          else
            return $ return v
    go changed (F v) = return $ return v
-}

freeze :: Core s -> TCM s (Core s)
freeze e = join <$> traverse go e
  where
    go v@(metaRef -> Just r) = either (const $ do mt <- freeze (metaType v); return $ return v {metaType = mt}) freeze =<< solution r
    go v                     = return $ return v

generalise :: Core s -> Core s -> TCM s (Core s, Core s)
generalise expr typ = do
  tr "generalise e" expr
  tr "           t" typ
  modifyIndent succ

  fvs <- foldMapM (:[]) typ
  l   <- level
  let p (metaRef -> Just r) = either (> l) (const False) <$> solution r
      p _                   = return False
  fvs' <- filterM p fvs

  deps <- M.fromList <$> forM fvs' (\x -> do
    ds <- foldMapM S.singleton $ metaType x
    return (x, ds)
   )
  let sorted = map go $ topoSort deps
  -- fexpr <- freeze expr
  -- ftyp  <- freeze typ
  genexpr <- F.foldrM ($ Core.etaLam) expr sorted
  gentype <- F.foldrM ($ Core.Pi)     typ  sorted

  modifyIndent pred
  tr "generalise res ge" genexpr
  tr "               gt" gentype
  return (genexpr, gentype)
  where
    go [a] f = fmap (f (metaHint a) Implicit $ metaType a) . abstract1M a
    go _   _ = error "Generalise"

inferType :: Input s -> TCM s (Core s, Core s)
inferType expr = do
  tr "inferType" expr
  modifyIndent succ
  (e, t) <- case expr of
    Input.Var v     -> return (Core.Var v, metaType v)
    Input.Type      -> return (Core.Type, Core.Type)
    Input.Pi n p Nothing s -> do
      tv  <- freshExistsV mempty Core.Type
      v   <- freshForall n tv
      (e', _)  <- checkType (instantiate1 (return v) s) Core.Type
      s'  <- abstract1M v e'
      return (Core.Pi n p tv s', Core.Type)
    Input.Pi n p (Just t) s -> do
      (t', _) <- checkType t Core.Type
      v  <- freshForall n t'
      (e', _) <- checkType (instantiate1 (return v) s) Core.Type
      s' <- abstract1M v e'
      return (Core.Pi n p t' s', Core.Type)
    Input.Lam n p s -> uncurry generalise <=< enterLevel $ do
      a   <- freshExistsV mempty Core.Type
      b   <- freshExistsV mempty Core.Type
      x   <- freshForall n a
      (e', b')  <- checkType (instantiate1 (return x) s) b
      s'  <- abstract1M x e'
      ab  <- abstract1M x b'
      return (Core.Lam n p a s', Core.Pi n p a ab)
    Input.App e1 p e2 -> do
      (e1', vt, s) <- inferPi e1 p
      (e2', _) <- checkType e2 vt
      return (Core.App e1' p e2', instantiate1 e2' s)
    Input.Anno e t  -> do
      (t', _) <- checkType t Core.Type
      checkType e t'
    Input.Wildcard  -> do
      t <- freshExistsV mempty Core.Type
      x <- freshExistsV mempty t
      return (x, t)
  modifyIndent pred
  tr "inferType res e" e
  tr "              t" t
  return (e, t)

occurs :: Level -> MetaVar s -> Core s -> TCM s ()
occurs l tv = traverse_ go
  where
    go tv'@(MetaVar _ typ _ mr)
      | tv == tv'                    = throwError "occurs check"
      | otherwise = do
        occurs l tv typ
        case mr of
          Nothing -> return ()
          Just r  -> do
            sol <- solution r
            case sol of
              Left l'    -> liftST $ writeSTRef r $ Left $ min l l'
              Right typ' -> occurs l tv typ'

unify :: Core s -> Core s -> TCM s ()
unify type1 type2 = do
  tr "unify t1" type1
  tr "      t2" type2
  go True type1 type2
  where
    go reduce t1 t2
      | t1 == t2  = return ()
      | otherwise = case (t1, t2) of
        (Core.Var v1@(metaRef -> Just r1), Core.Var v2@(metaRef -> Just r2)) -> do
          unify (metaType v1) (metaType v2)
          sol1 <- solution r1
          sol2 <- solution r2
          case (sol1, sol2) of
            (Left l1, Left l2)
              | l1 <= l2  -> solve r2 t1
              | otherwise -> solve r1 t2
            (Right c1, _) -> go reduce c1 t2
            (_, Right c2) -> go reduce t1 c2
        -- If we have 'unify (f xs) t', where 'f' is an existential, and 'xs'
        -- are distinct universally quantified variables, then 'f = \xs. t' is
        -- a most general solution (See Miller, Dale (1991) "A Logic
        -- programming...")
        (Core.appsView -> (Core.Var v@(metaRef -> Just r), distinctForalls -> Just pvs), _) -> solveVar r v pvs t2
        (_, Core.appsView -> (Core.Var v@(metaRef -> Just r), distinctForalls -> Just pvs)) -> solveVar r v pvs t1
        (Core.Pi  h p1 a s1, Core.Pi  _ p2 b s2) | p1 == p2 -> absCase h a b s1 s2
        (Core.Lam h p1 a s1, Core.Lam _ p2 b s2) | p1 == p2 -> absCase h a b s1 s2

        -- If we've already tried reducing the application,
        -- we can only hope to unify it pointwise.
        (Core.App e1 p1 e1', Core.App e2 p2 e2') | p1 == p2 && not reduce -> do
          go True e1  e2
          go True e1' e2'
        (Core.Type, Core.Type) -> return ()
        _ | reduce             -> do
          t1' <- whnf t1
          t2' <- whnf t2
          go False t1' t2'
        _                      -> throwError "Can't unify types"
    absCase h a b s1 s2 = do
      go True a b
      v <- freshForall h a
      go True (instantiate1 (return v) s1) (instantiate1 (return v) s2)
    distinctForalls pes | distinct pes = traverse isForall pes
                        | otherwise    = Nothing
    isForall (p, Core.Var v@(metaRef -> Nothing)) = Just (p, v)
    isForall _                                    = Nothing
    distinct pes = S.size (S.fromList es) == length es where es = map snd pes
    solveVar r v pvs t = do
      sol <- solution r
      case sol of
        Left l  -> do
          occurs l v t
          solve r =<< lams pvs t
        Right c -> go True (Core.apps c (map (second return) pvs)) t
    lams pvs t = F.foldrM (\(p, v) -> fmap (Core.Lam (Hint Nothing) p $ metaType v) . abstract1M v) t pvs


subtype :: Core s -> Core s -> Core s -> TCM s (Core s, Core s)
subtype expr type1 type2 = do
  tr "subtype e"  expr
  tr "        t1" type1
  tr "        t2" type2
  modifyIndent succ
  (e', type') <- go True expr type1 type2
  modifyIndent pred
  tr "subtype res e'" e'
  tr "            type'" type'
  return (e', type')
  where
    go reduce e typ1 typ2
      | typ1 == typ2 = return (e, typ2)
      | otherwise = case (typ1, typ2) of
        (Core.Pi h1 p1 t1 s1, Core.Pi h2 p2 t2 s2) | p1 == p2 -> do
          let h = h1 <> h2
          x2  <- freshForall h t2
          (x1, _)   <- subtype (return x2) t2 t1
          (ex, s2') <- subtype (Core.App e p1 x1)
                                (instantiate1 x1 s1)
                                (instantiate1 x1 s2)
          e2    <- Core.etaLam h p1 t2 <$> abstract1M x2 ex
          typ2' <- Core.Pi h p1 t2 <$> abstract1M x2 s2'
          return (e2, typ2')
        {-
        (Core.Pi n p t1 s1, Core.Var v@(metaRef -> Just r)) -> do
          sol <- solution r
          case sol of
            Left l -> do
              occurs l v typ1
              unify (metaType v) Core.Type
              t2  <- freshExistsLV Core.Type l
              t2' <- freshExistsLV Core.Type l
              x2  <- freshExists t2
              solve r . Core.Pi n p t2 =<< abstract1M x2 t2'
              x1  <- subtype (return x2) t2 t1
              ex  <- subtype (Core.App e p x1) (instantiate1 x1 s1) t2'
              refineSolved r . Core.Pi n p t2 =<< abstract1M x2 t2'
              Core.etaLam n p t2 <$> abstract1M x2 ex
            Right c -> subtype e typ1 c
        -}
        (Core.Var v@(metaRef -> Just r), Core.Pi h p t2 s2) -> do
          sol <- solution r
          case sol of
            Left l -> do
              occurs l v typ2
              unify (metaType v) Core.Type
              t11  <- freshExistsLV (metaHint v) Core.Type l
              t12 <- freshExistsLV (metaHint v) Core.Type l
              solve r $ Core.Pi h p t11 $ abstractNothing t12
              x2  <- freshForall h t2
              (x1, t11') <- subtype (return x2) t2 t11
              (ex, s2')  <- subtype (Core.betaApp e p x1) t12 (instantiate1 (return x2) s2)
              refineSolved r . Core.Pi h p t11' =<< abstract1M x2 s2'
              e2    <- Core.etaLam h p t2 <$> abstract1M x2 ex
              typ2' <- Core.Pi h p t2 <$> abstract1M x2 s2'
              return (e2, typ2')
            Right c -> subtype e c typ2
        (_, Core.Pi h Implicit t2 s2) -> do
          x2 <- freshForall h t2
          (e2, s2') <- subtype e typ1 (instantiate1 (return x2) s2)
          e2'   <- Core.etaLam h Implicit t2 <$> abstract1M x2 e2
          typ2' <- Core.Pi     h Implicit t2 <$> abstract1M x2 s2'
          return (e2', typ2')
        (Core.Pi h Implicit t1 s1, _) -> do
          v1 <- freshExistsV h t1
          subtype (Core.betaApp e Implicit v1) (instantiate1 v1 s1) typ2
        _ | reduce -> do
          typ1' <- whnf typ1
          typ2' <- whnf typ2
          go False e typ1' typ2'
        _ -> do unify typ1 typ2; return (e, typ2)

checkType :: Input s -> Core s -> TCM s (Core s, Core s)
checkType expr typ = do
  tr "checkType e" expr
  tr "          t" =<< freeze typ
  modifyIndent succ
  (rese, rest) <- case expr of
    Input.Lam m p s -> do
      typ' <- whnf typ
      case typ' of
        Core.Pi h p' a ts | p == p' -> do
          v <- freshForall h a
          (body, ts') <- checkType (instantiate1 (return v) s)
                                   (instantiate1 (return v) ts)
          expr' <- Core.Lam m p a <$> abstract1M v body
          typ'' <- Core.Pi m p a <$> abstract1M v ts'
          return (expr', typ'')
        _ -> inferIt
    _ -> inferIt
  modifyIndent pred
  tr "checkType res e" rese
  tr "              t" rest
  return (rese, rest)
    where
      inferIt = do
        (expr', typ') <- inferType expr
        subtype expr' typ' typ

data Empty
fromEmpty :: Empty -> a
fromEmpty = error "fromEmpty"

infer :: Input.Expr Empty -> (Either String (Doc, Doc), [String])
infer e = runTCM
        $ bimapM showMeta showMeta <=< bimapM freeze freeze <=< uncurry generalise <=< (enterLevel . inferType)
        $ fmap fromEmpty e

test :: String -> IO ()
test inp = case (infer . fmap (const undefined)) <$> Parser.test Parser.expr inp of
  Success (res, l) -> do
    putDoc $ pretty l
    putStrLn ""
    putStrLn ""
    putDoc $ pretty res
    putStrLn ""
  Failure d        -> putDoc d
