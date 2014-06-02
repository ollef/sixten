{-# LANGUAGE ViewPatterns #-}
module Infer where

import Bound
import Control.Applicative
import Control.Monad.Error
import Control.Monad.ST()
import Control.Monad.ST.Class
import Data.Bitraversable
import Data.Either
import Data.Foldable as F
import Data.Function
import qualified Data.Map as M
import qualified Data.Set as S
import Data.STRef
import Data.Traversable

import qualified Core
import qualified Input
import Monad
import TopoSort
import Util

type Input s = Input.Expr (MetaVar s)
type Core  s = Core.Expr  (MetaVar s)

type Exists s = STRef s (Either Level (Core s))

data MetaVar s = MetaVar
  { metaId   :: !Int
  , metaType :: Core s
  , metaRef  :: !(Maybe (Exists s))
  }

instance Eq (MetaVar s) where
  (==) = (==) `on` metaId

instance Ord (MetaVar s) where
  compare = compare `on` metaId

instance Show (MetaVar s) where
  showsPrec d (MetaVar i a _) = showParen (d > 10) $
    showString "Meta" . showChar ' ' . showsPrec 11 i .
    showChar ' ' . showsPrec 11 a . showChar ' ' . showString "<Ref>"

freshExists :: Core s -> TCM s (MetaVar s)
freshExists a = do
  l   <- level
  i   <- fresh
  ref <- liftST $ newSTRef $ Left l
  return $ MetaVar i a (Just ref)

freshExistsV :: Monad g => Core s -> TCM s (g (MetaVar s))
freshExistsV a = return <$> freshExists a

freshForall :: Core s -> TCM s (MetaVar s)
freshForall a = MetaVar <$> fresh <*> pure a <*> pure Nothing

freshForallV :: Monad g => Core s -> TCM s (g (MetaVar s))
freshForallV a = return <$> freshForall a

refine :: Exists s -> Core s -> (Core s -> TCM s (Core s)) -> TCM s (Core s)
refine r d f = solution r >>=
  either (const $ return d) (\e -> do
    e' <- f e
    liftST $ writeSTRef r (Right e')
    return e'
  )

solution :: Exists s -> TCM s (Either Level (Core s))
solution = liftST . readSTRef

{-
isUnsolved :: MetaRef s -> TCM s Bool
isUnsolved v = not <$> isSolved v
-}

isSolved :: Exists s -> TCM s Bool
isSolved r = isRight <$> solution r

solve :: Exists s -> Core s -> TCM s ()
solve r x = do
  whenM (isSolved r) $ throwError "Trying to solve something already solved"
  liftST $ writeSTRef r $ Right x

freshLet :: Core s -> Core s -> TCM s (MetaVar s)
freshLet e t = do
  i   <- fresh
  ref <- liftST $ newSTRef $ Right e
  return $ MetaVar i t (Just ref)

freshLetV :: Monad g => Core s -> Core s -> TCM s (g (MetaVar s))
freshLetV e t = return <$> freshLet e t

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
      Core.Lam _ p' t2 s | p == p' -> do
        e2' <- freshLetV e2 t2
        whnf $ instantiate1 e2' s
      _ -> return expr

normalise :: Core s -> TCM s (Core s)
normalise expr = case expr of
  Core.Var (metaRef -> Nothing) -> return expr
  Core.Var (metaRef -> Just r)  -> refine r expr normalise
  Core.Var _                    -> throwError "normalise impossible"
  Core.Type                     -> return Core.Type
  Core.Pi n p a s               -> normaliseScope (Core.Pi n p) a s
  Core.Lam n p a s              -> normaliseScope (Core.Lam n p) a s
  Core.App e1 p e2              -> do
    e1' <- normalise e1
    e2' <- normalise e2
    case e1' of
      Core.Lam _ p' _ s | p == p' -> normalise $ instantiate1 e2' s
      _                           -> return $ Core.App e1' p e2'
  where
    normaliseScope c a s = do
      x <- freshForall a
      c a <$> abstract1 x <$> normalise (instantiate1 (return x) s)

inferPi :: Input s -> Plicitness -> TCM s (Core s, Core s, Scope1 Core.Expr (MetaVar s))
inferPi expr p = do
  (e, t) <- inferType expr
  go True e t
  where
    go reduce e t = case t of
      Core.Pi _ p' vt s | p == p' -> return (e, vt, s)
      Core.Pi _ Implicit vt s     -> do
        v <- freshExistsV vt
        go True (Core.App e Implicit v) (instantiate1 v s)
      Core.Var v@(metaRef -> Just r) -> do
        sol <- solution r
        case sol of
          Left _ -> do
            unify (metaType v) Core.Type
            t1  <- freshExistsV Core.Type
            t2  <- freshExistsV Core.Type
            x   <- freshExists t1
            return (e, t1, abstract1 x t2)
          Right c -> go True e c
      _ | reduce                  -> go False e =<< whnf t
      _                           -> throwError "Function needed!"

freeze :: Core s -> TCM s (Core s)
freeze e = join <$> traverse go e
  where
    go v@(metaRef -> Just r) = do
      sol <- solution r
      case sol of
        Left _  -> return $ return v
        Right c -> return c
    go v                     = return $ return v

generalise :: Core s -> Core s -> TCM s (Core s, Core s)
generalise expr typ = do
  expr' <- freeze expr -- TODO Shouldn't need to freeze everything
  typ'  <- freeze typ
  let fvs = foldMap (:[]) typ'
  l    <- level
  let p (metaRef -> Just r) = do
        sol <- solution r
        case sol of
          Left l' -> return $ l' > l
          Right _ -> return False
      p _ = return False
  fvs' <- filterM p fvs
  let deps   = M.fromList [(x, foldMap S.singleton $ metaType x) | x <- fvs']
      sorted = map go $ topoSort deps
      go [a] = ("$" ++ show (metaId a), a, metaType a)
      go _   = error "Generalise"
  return ( F.foldr (\(n, x, t) -> Core.Lam n Implicit t . abstract1 x) expr' sorted
         , F.foldr (\(n, x, t) -> Core.Pi  n Implicit t . abstract1 x) typ'  sorted
         )

inferType :: Input s -> TCM s (Core s, Core s)
inferType expr = case expr of
  Input.Var v     -> return (Core.Var v, metaType v)
  Input.Type      -> return (Core.Type, Core.Type)
  Input.Pi n p s  -> do
    v <- freshExists Core.Type
    (e', _) <- inferType $ instantiate1 (return v) s
    return (Core.Pi n p Core.Type (abstract1 v e'), Core.Type)
  Input.Lam n p s -> uncurry generalise <=< enterLevel $ do
    a  <- freshExistsV Core.Type
    b  <- freshExistsV Core.Type
    x  <- freshForall a
    e' <- checkType (instantiate1 (return x) s) b
    return (Core.Lam n p a $ abstract1 x e', Core.Pi  n p a $ abstract1 x b)
  Input.App e1 p e2 -> do
    (e1', vt, s) <- inferPi e1 p
    (e2', t2) <- inferType e2
    e2'' <- subtype e2' t2 vt
    return (Core.App e1' p e2'', instantiate1 e2'' s)
  Input.Anno e t  -> do
    t' <- checkType t Core.Type
    e' <- checkType e t'
    return (e', t')
  Input.Wildcard  -> do
    t <- freshExistsV Core.Type
    x <- freshExistsV t
    return (x, t)

occurs :: Level -> MetaVar s -> Core s -> TCM s ()
occurs l tv = traverse_ go
  where
    go tv'@(MetaVar _ typ mr)
      | tv == tv' = throwError "occurs check"
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
unify = go True
  where
    go reduce t1 t2
      | t1 == t2  = return ()
      | otherwise = case (t1, t2) of
        (Core.Var v@(metaRef -> Just r), _) -> solveVar r v t2
        (_, Core.Var v@(metaRef -> Just r)) -> solveVar r v t1
        (Core.Pi  _ p1 a s1, Core.Pi  _ p2 b s2) | p1 == p2 -> absCase a b s1 s2
        (Core.Lam _ p1 a s1, Core.Lam _ p2 b s2) | p1 == p2 -> absCase a b s1 s2
        (Core.App e1 p1 e1', Core.App e2 p2 e2') | p1 == p2-> do
          go True e1 e2
          go True e1' e2'
        (Core.Type, Core.Type) -> return ()
        _ | reduce             -> do
          t1' <- whnf t1
          t2' <- whnf t2
          go False t1' t2'
        _                      -> throwError "Can't unify types"
    absCase a b s1 s2 = do
      go True a b
      v <- freshForallV a
      go True (instantiate1 v s1) (instantiate1 v s2)
    solveVar r v t = do
      sol <- solution r
      case sol of
        Left l  -> do occurs l v t; solve r t
        Right c -> go True c t

subtype :: Core s -> Core s -> Core s -> TCM s (Core s)
subtype = go True
  where
    go reduce e typ1 typ2
      | typ1 == typ2 = return e
      | otherwise = case (typ1, typ2) of
        (Core.Pi n p1 t1 s1, Core.Pi _ p2 t2 s2) | p1 == p2 -> do
          x  <- freshForall t2
          x' <- subtype (return x) t2 t1
          ex <- subtype (Core.App e p1 x') (instantiate1 x' s1)
                                           (instantiate1 x' s2)
          return $ Core.Lam n p1 t2 $ abstract1 x ex
        (Core.Pi n p t1 s1, Core.Var v@(metaRef -> Just r)) -> do
          sol <- solution r
          case sol of
            Left l -> do
              occurs l v typ1
              unify (metaType v) Core.Type
              t2  <- freshExistsV Core.Type
              t2' <- freshExistsV Core.Type
              x   <- freshExists t2
              x'  <- subtype (return x) t2 t1
              ex  <- subtype (Core.App e p x') (instantiate1 x' s1) t2'
              solve r $ Core.Pi n p t2 (abstract1 x t2')
              return $ Core.Lam n p t2 $ abstract1 x ex
            Right c -> subtype e typ1 c
        (Core.Var v@(metaRef -> Just r), Core.Pi n p t2 s2) -> do
          sol <- solution r
          case sol of
            Left l -> do
              occurs l v typ2
              unify (metaType v) Core.Type
              t1  <- freshExistsV Core.Type
              t1' <- freshExistsV Core.Type
              x   <- freshExists t1
              x'  <- subtype (return x) t2 t1
              ex  <- subtype (Core.App e p x') t1' (instantiate1 x' s2)
              return $ Core.Lam n p t2 $ abstract1 x ex
            Right c -> subtype e c typ2
        (_, Core.Pi _ _ t2 s2) -> do
          v <- freshForallV t2
          subtype e typ1 (instantiate1 v s2)
        (Core.Pi _ p1 t1 s2, _) -> do
          v <- freshExists t1
          subtype (Core.App e p1 $ return v) (instantiate1 (return v) s2) typ2
        _ | reduce -> do
          typ1' <- whnf typ1
          typ2' <- whnf typ2
          go False e typ1' typ2'
        _ -> do unify typ1 typ2; return e

checkType :: Input s -> Core s -> TCM s (Core s)
checkType expr typ = case expr of
  Input.Lam m p s -> do
    typ' <- whnf typ
    case typ' of
      Core.Pi _ p' a ts | p == p' -> do
        v <- freshForall a
        body <- checkType (instantiate1 (return v) s)
                          (instantiate1 (return v) ts)
        return $ Core.Lam m p a $ abstract1 v body
      _ -> inferIt
  _ -> inferIt
  where
    inferIt = do
      (expr', typ') <- inferType expr
      subtype expr' typ' typ

data Empty
fromEmpty :: Empty -> a
fromEmpty = error "fromEmpty"

infer :: Input.Expr Empty -> Either String (Core.Expr Int, Core.Expr Int)
infer e = evalTCM
        $ fmap (\(x, y) -> (metaId <$> x, metaId <$> y))
        $ inferType >=> bimapM freeze freeze
        $ fmap fromEmpty e
