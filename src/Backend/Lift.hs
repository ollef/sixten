{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module Backend.Lift where

import Protolude

import Control.Lens hiding (Context)
import Control.Monad.Except
import Control.Monad.Reader
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Rock

import Driver.Query
import Effect
import Effect.Context as Context
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

-- TODO do we need Sequential here?
newtype Lift thing a = Lift (StateT (LiftState thing) (ReaderT (ContextEnvT (Lifted.Expr FreeVar) VIX.Env) (Sequential (Task Query))) a)
  deriving (Functor, Applicative, Monad, MonadState (LiftState thing), MonadFresh, MonadIO, MonadLog, MonadFetch Query, MonadContext (Lifted.Expr FreeVar))

freshName :: Lift thing GName
freshName = do
  s <- get
  case freshNames s of
    [] -> panic "Lift: no more fresh names"
    name:names -> do
      put s { freshNames = names }
      return $ case baseName s of
        GName qn parts -> GName qn $ parts <> pure name

freshNameWithHint :: Name -> Lift thing GName
freshNameWithHint hint = do
  s <- get
  case freshNames s of
    [] -> panic "Lift: no more fresh names"
    name:names -> do
      put s { freshNames = names }
      return $ case baseName s of
        GName qn parts ->
          GName qn $ parts <> pure (name <> "-" <> hint)

liftNamedThing :: GName -> thing -> Lift thing ()
liftNamedThing name thing =
  modify $ \s -> s
    { liftedThings = (name, thing) : liftedThings s
    }

liftThing :: thing -> Lift thing GName
liftThing thing = do
  name <- freshName
  liftNamedThing name thing
  return name

runLift
  :: GName
  -> Name
  -> Lift thing a
  -> VIX (a, [(GName, thing)])
runLift gn postfix (Lift l)
  = withContextEnvT
  $ second liftedThings
  <$> runStateT l LiftState
  { baseName = gn
  , freshNames = (postfix <>) . shower <$> [(0 :: Int)..]
  , liftedThings = mempty
  }

type LambdaLift = Lift (Closed (Sized.Function Lifted.Expr))

liftExpr
  :: SLambda.Expr FreeVar
  -> LambdaLift (Lifted.Expr FreeVar)
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
  :: Anno SLambda.Expr FreeVar
  -> LambdaLift (Anno Lifted.Expr FreeVar)
liftAnnoExpr (Anno e t) = Anno <$> liftExpr e <*> liftExpr t

liftLambda
  :: Telescope SLambda.Expr FreeVar
  -> AnnoScope TeleVar SLambda.Expr FreeVar
  -> LambdaLift (Lifted.Expr FreeVar)
liftLambda tele lamScope = do
  sortedFvs <- topoSortVars $ toHashSet tele <> toHashSet lamScope

  closeLambda tele lamScope sortedFvs $ \params lamBody -> do
    context <- getContext
    let
      args = (`varAnno` context) <$> sortedFvs
      addArgs
        | null args = identity
        | otherwise = (`Lifted.Call` args)

    fun <- Sized.function params lamBody

    g <- liftThing $ close (panic "liftLambda not closed") fun

    return $ addArgs $ global g

closeLambda
  :: Telescope SLambda.Expr FreeVar
  -> AnnoScope TeleVar SLambda.Expr FreeVar
  -> Vector FreeVar
  -> (Vector FreeVar -> Anno Lifted.Expr FreeVar -> LambdaLift a)
  -> LambdaLift a
closeLambda tele lamScope sortedFvs k =
  teleMapExtendContext tele liftExpr $ \vs -> do
    let lamExpr = instantiateAnnoTele pure vs lamScope
    lamExpr' <- liftAnnoExpr lamExpr

    k (sortedFvs <> vs) lamExpr'

topoSortVars
  :: (MonadContext (e FreeVar) m, Foldable e)
  => HashSet FreeVar
  -> m (Vector FreeVar)
topoSortVars vs = do
  context <- getContext
  return
    $ Vector.fromList
    $ fmap acyclic
    $ topoSortWith identity (toHashSet . (`Context.lookupType` context))
    $ HashSet.toList vs
  where
    acyclic (AcyclicSCC a) = a
    acyclic (CyclicSCC _) = panic "topoSortVars"

liftLet
  :: LetRec SLambda.Expr FreeVar
  -> Scope LetVar SLambda.Expr FreeVar
  -> LambdaLift (Lifted.Expr FreeVar)
liftLet ds scope =
  letMapExtendContext ds liftExpr $ \vs -> do
    context <- getContext
    let
      instantiatedDs = Vector.zip vs $ instantiateLet pure vs <$> letBodies ds
      dsToLift = [(v, body) | (v, body@(SLambda.lamView -> Just _)) <- toList instantiatedDs]
      liftedVars = toHashSet $ fst <$> dsToLift
      fvs = fold (toHashSet . snd <$> dsToLift) `HashSet.difference` liftedVars

    sortedFvs <- topoSortVars fvs
    let
      args = (`varAnno` context) <$> sortedFvs
      addArgs
        | null args = identity
        | otherwise = (`Lifted.Call` args)

    subVec <- forM (toVector dsToLift) $ \(v, _) -> do
      g <- fromNameHint freshName freshNameWithHint $ Context.lookupHint v context
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
          let
            g = case varIndex v of
              Just i -> snd $ subVec Vector.! i
              Nothing -> panic "liftLet g"
          closeLambda (subBound lamTele) (subBound lamScope) sortedFvs $ \params lamBody -> do
            fun <- Sized.function params lamBody
            liftNamedThing g $ close (panic "liftLet not closed") fun
            return $ addArgs $ global g
        _ -> liftExpr $ subBind body

    letBody <- liftExpr (subBind $ instantiateLet pure vs scope)

    let
      sortedDs = topoSortWith fst (toHashSet . snd) (Vector.zip vs liftedDs)

    lets sortedDs letBody

liftBranches
  :: Branches SLambda.Expr FreeVar
  -> LambdaLift (Branches Lifted.Expr FreeVar)
liftBranches (ConBranches cbrs) = fmap ConBranches $
  forM cbrs $ \(ConBranch qc tele brScope) ->
    teleMapExtendContext tele liftExpr $ \vs -> do
      let brExpr = instantiateTele pure vs brScope
      brExpr' <- liftExpr brExpr
      conBranch qc vs brExpr'
liftBranches (LitBranches lbrs def) = LitBranches
  <$> mapM (\(LitBranch l e) -> LitBranch l <$> liftExpr e) lbrs <*> liftExpr def

lets
  :: MonadContext (Lifted.Expr FreeVar) m
  => [SCC (FreeVar, Lifted.Expr FreeVar)]
  -> Lifted.Expr FreeVar
  -> m (Lifted.Expr FreeVar)
lets = flip $ foldrM go
  where
    go (AcyclicSCC (v, e)) = Lifted.let_ v e
    go _ = panic "Circular Lift lets"

liftToDefinitionM
  :: Closed (Anno SLambda.Expr)
  -> LambdaLift (Closed (Sized.Definition Lifted.Expr))
liftToDefinitionM (Closed (Anno (SLambda.Lams tele bodyScope) _)) =
  teleMapExtendContext tele liftExpr $ \vs -> do
    let body = instantiateAnnoTele pure vs bodyScope
    body' <- liftAnnoExpr body
    fun <- Sized.function vs body'
    return
      $ close (panic "liftToDefinitionM")
      $ Sized.FunctionDef Public Sized.NonClosure fun
liftToDefinitionM (Closed sexpr) = do
  sexpr' <- liftAnnoExpr sexpr
  return
    $ close (panic "liftToDefinitionM 2")
    $ Sized.ConstantDef Public
    $ Sized.Constant sexpr'

liftToDefinition
  :: GName
  -> Closed (Anno SLambda.Expr)
  -> VIX [(GName, Closed (Sized.Definition Lifted.Expr))]
liftToDefinition name expr = do
  (def, fs) <- runLift name "lifted" $ liftToDefinitionM expr
  return
    $ (name, def)
    : fmap (second $ mapClosed $ Sized.FunctionDef Private Sized.NonClosure) fs
