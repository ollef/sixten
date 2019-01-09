{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Backend.Lift where

import Protolude

import Control.Monad.Except
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Rock

import Effect
import Syntax
import Syntax.Sized.Anno
import qualified Syntax.Sized.Definition as Sized
import qualified Syntax.Sized.Lifted as Lifted
import qualified Syntax.Sized.SLambda as SLambda
import TypedFreeVar
import Util
import Util.TopoSort
import VIX

data LiftState thing = LiftState
  { baseName :: !GName
  , freshNames :: [Name]
  , liftedThings :: [(GName, thing)]
  }

newtype Lift thing m a = Lift (StateT (LiftState thing) m a)
  deriving (Functor, Applicative, Monad, MonadState (LiftState thing), MonadTrans, MonadFresh, MonadIO, MonadLog, MonadFetch q)

freshName :: Monad m => Lift thing m GName
freshName = do
  s <- get
  case freshNames s of
    [] -> panic "Lift: no more fresh names"
    name:names -> do
      put s { freshNames = names }
      return $ case baseName s of
        GName qn parts -> GName qn $ parts <> pure name

freshNameWithHint :: Monad m => Name -> Lift thing m GName
freshNameWithHint hint = do
  s <- get
  case freshNames s of
    [] -> panic "Lift: no more fresh names"
    name:names -> do
      put s { freshNames = names }
      return $ case baseName s of
        GName qn parts ->
          GName qn $ parts <> pure (name <> "-" <> hint)

liftNamedThing :: Monad m => GName -> thing -> Lift thing m ()
liftNamedThing name thing =
  modify $ \s -> s
    { liftedThings = (name, thing) : liftedThings s
    }

liftThing :: Monad m => thing -> Lift thing m GName
liftThing thing = do
  name <- freshName
  liftNamedThing name thing
  return name

runLift
  :: Functor m
  => GName
  -> Name
  -> Lift thing m a
  -> m (a, [(GName, thing)])
runLift gn postfix (Lift l)
  = second liftedThings
  <$> runStateT l LiftState
  { baseName = gn
  , freshNames = (postfix <>) . shower <$> [(0 :: Int)..]
  , liftedThings = mempty
  }

type FV = FreeVar Lifted.Expr

type LambdaLift = Lift (Closed (Sized.Function Lifted.Expr)) VIX

liftExpr
  :: SLambda.Expr FV
  -> LambdaLift (Lifted.Expr FV)
liftExpr expr = case expr of
  SLambda.Var v -> return $ Lifted.Var v
  SLambda.Global g -> return $ Lifted.Global g
  SLambda.Lit l -> return $ Lifted.Lit l
  SLambda.Con qc es -> Lifted.Con qc <$> mapM liftAnnoExpr es
  SLambda.App e1 e2 -> Lifted.Call <$> liftExpr e1 <*> (pure <$> liftAnnoExpr e2)
  SLambda.Let ds scope -> liftLet ds scope
  SLambda.Case e brs -> Lifted.Case <$> liftAnnoExpr e <*> liftBranches brs
  SLambda.Lams tele s -> liftLambda tele s
  SLambda.Lam {} -> panic "liftExpr Lam"
  SLambda.ExternCode c retType -> Lifted.ExternCode <$> mapM liftAnnoExpr c <*> liftExpr retType

liftAnnoExpr
  :: Anno SLambda.Expr FV
  -> LambdaLift (Anno Lifted.Expr FV)
liftAnnoExpr (Anno e t) = Anno <$> liftExpr e <*> liftExpr t

liftLambda
  :: Telescope SLambda.Expr FV
  -> AnnoScope TeleVar SLambda.Expr FV
  -> LambdaLift (Lifted.Expr FV)
liftLambda tele lamScope = do
  logFreeVar "lift" "liftLambda" $ Sized.Function tele lamScope

  let sortedFvs = topoSortVars $ toHashSet tele <> toHashSet lamScope

  (params, lamBody) <- closeLambda tele lamScope sortedFvs

  let args = (\v -> Anno (pure v) (varType v)) <$> sortedFvs
      addArgs
        | null args = identity
        | otherwise = (`Lifted.Call` args)

  let fun = Sized.functionTyped params lamBody
  logFreeVar "lift" "liftLambda result" fun

  g <- liftThing $ close (panic "liftLambda not closed") fun

  return $ addArgs $ global g

closeLambda
  :: Telescope SLambda.Expr FV
  -> AnnoScope TeleVar SLambda.Expr FV
  -> Vector FV
  -> LambdaLift (Vector FV, Anno Lifted.Expr FV)
closeLambda tele lamScope sortedFvs = do
  vs <- forTeleWithPrefixM tele $ \h p s vs -> do
    let e = instantiateTele pure vs s
    e' <- liftExpr e
    freeVar h p e'

  let lamExpr = instantiateAnnoTele pure vs lamScope
  lamExpr' <- liftAnnoExpr lamExpr

  return (sortedFvs <> vs, lamExpr')

topoSortVars
  :: HashSet FV
  -> Vector FV
topoSortVars vs
  = Vector.fromList
  $ fmap acyclic
  $ topoSortWith identity (toHashSet . varType)
  $ HashSet.toList vs
  where
    acyclic (AcyclicSCC a) = a
    acyclic (CyclicSCC _) = panic "topoSortVars"

liftLet
  :: LetRec SLambda.Expr FV
  -> Scope LetVar SLambda.Expr FV
  -> LambdaLift (Lifted.Expr FV)
liftLet ds scope = do
  vs <- forMLet ds $ \h _ _ t -> do
    t' <- liftExpr t
    freeVar h Explicit t'

  let instantiatedDs = Vector.zip vs $ instantiateLet pure vs <$> letBodies ds
      dsToLift = [(v, body) | (v, body@(SLambda.lamView -> Just _)) <- toList instantiatedDs]
      liftedVars = toHashSet $ fst <$> dsToLift
      fvs = fold (toHashSet . snd <$> dsToLift) `HashSet.difference` liftedVars
      sortedFvs = topoSortVars fvs
      args = (\v -> Anno (pure v) (varType v)) <$> sortedFvs
      addArgs
        | null args = identity
        | otherwise = (`Lifted.Call` args)

  subVec <- forM (toVector dsToLift) $ \(v, _) -> do
    g <- fromNameHint freshName freshNameWithHint $ varHint v
    return (v, g)

  logShow "lift" "subVec" subVec
  logShow "lift" "sortedFvs" fvs

  let varIndex = hashedElemIndex $ fst <$> subVec
      go v = case varIndex v of
        Just i -> global $ snd $ subVec Vector.! i
        Nothing -> pure v
      subBind e
        | Vector.null subVec = e
        | otherwise = e >>= go
      subBound e
        | Vector.null subVec = e
        | otherwise = e >>>= go

  liftedDs <- forM instantiatedDs $ \(v, body) ->
    case body of
      SLambda.Lams lamTele lamScope -> do
        let g = case varIndex v of
              Just i -> snd $ subVec Vector.! i
              Nothing -> panic "liftLet g"
        (params, lamBody) <- closeLambda (subBound lamTele) (subBound lamScope) sortedFvs
        liftNamedThing g $ close (panic "liftLet not closed") $ Sized.functionTyped params lamBody
        return $ addArgs $ global g
      _ -> liftExpr $ subBind body

  letBody <- liftExpr (subBind $ instantiateLet pure vs scope)

  let sortedDs = topoSortWith fst (toHashSet . snd) (Vector.zip vs liftedDs)

  return $ lets sortedDs letBody

liftBranches
  :: Branches SLambda.Expr FV
  -> LambdaLift (Branches Lifted.Expr FV)
liftBranches (ConBranches cbrs) = fmap ConBranches $
  forM cbrs $ \(ConBranch qc tele brScope) -> do
    vs <- forTeleWithPrefixM tele $ \h p s vs -> do
      let e = instantiateTele pure vs s
      e' <- liftExpr e
      freeVar h p e'
    let brExpr = instantiateTele pure vs brScope
    brExpr' <- liftExpr brExpr
    return $ conBranchTyped qc vs brExpr'
liftBranches (LitBranches lbrs def) = LitBranches
  <$> mapM (\(LitBranch l e) -> LitBranch l <$> liftExpr e) lbrs <*> liftExpr def

lets
  :: [SCC (FV, Lifted.Expr FV)]
  -> Lifted.Expr FV
  -> Lifted.Expr FV
lets = flip $ foldr go
  where
    go (AcyclicSCC (v, e)) = Lifted.letTyped v e
    go _ = panic "Circular Lift lets"

liftToDefinitionM
  :: Closed (Anno SLambda.Expr)
  -> LambdaLift (Closed (Sized.Definition Lifted.Expr))
liftToDefinitionM (Closed (Anno (SLambda.Lams tele bodyScope) _)) = do
  vs <- forTeleWithPrefixM tele $ \h p s vs -> do
    let e = instantiateTele pure vs s
    e' <- liftExpr e
    freeVar h p e'
  let body = instantiateAnnoTele pure vs bodyScope
  body' <- liftAnnoExpr body
  return
    $ close (panic "liftToDefinitionM")
    $ Sized.FunctionDef Public Sized.NonClosure
    $ Sized.functionTyped vs body'
liftToDefinitionM (Closed sexpr) = do
  sexpr' <- liftAnnoExpr sexpr
  logFreeVar "lift" "liftToDefinitionM sexpr'" sexpr'
  return
    $ close (panic "liftToDefinitionM 2")
    $ Sized.ConstantDef Public
    $ Sized.Constant sexpr'

liftToDefinition
  :: GName
  -> Closed (Anno SLambda.Expr)
  -> VIX [(GName, Closed (Sized.Definition Lifted.Expr))]
liftToDefinition name expr = do
  (def, fs) <- runLift name "lifted" (liftToDefinitionM expr)
  return
    $ (name, def)
    : fmap (second $ mapClosed $ Sized.FunctionDef Private Sized.NonClosure) fs
