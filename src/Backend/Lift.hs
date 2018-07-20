{-# LANGUAGE GeneralizedNewtypeDeriving, OverloadedStrings, MonadComprehensions, ViewPatterns #-}
module Backend.Lift where

import Control.Monad.Except
import Control.Monad.Fail
import Control.Monad.State
import Data.Bifunctor
import Data.Foldable
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import MonadFresh
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
  { freshNames :: [QName]
  , liftedThings :: [(QName, thing)]
  }

newtype Lift thing m a = Lift (StateT (LiftState thing) m a)
  deriving (Functor, Applicative, Monad, MonadState (LiftState thing), MonadTrans, MonadFail, MonadFresh, MonadVIX, MonadIO, MonadError e)

freshName :: MonadFail m => Lift thing m QName
freshName = do
  name:names <- gets freshNames
  modify $ \s -> s { freshNames = names }
  return name

freshNameWithHint :: MonadFail m => Name -> Lift thing m QName
freshNameWithHint hint = do
  QName mname name:names <- gets freshNames
  modify $ \s -> s { freshNames = names }
  return $ QName mname $ name <> "-" <> hint

liftNamedThing :: Monad m => QName -> thing -> Lift thing m ()
liftNamedThing name thing =
  modify $ \s -> s
    { liftedThings = (name, thing) : liftedThings s
    }

liftThing :: MonadFail m => thing -> Lift thing m QName
liftThing thing = do
  name <- freshName
  liftNamedThing name thing
  return name

runLift
  :: Functor m
  => QName
  -> Lift thing m a
  -> m (a, [(QName, thing)])
runLift (QName mname name) (Lift l)
  = second liftedThings
  <$> runStateT l LiftState
  { freshNames = [QName mname $ name <> if n == 0 then "" else shower n | n <- [(0 :: Int)..]]
  , liftedThings = mempty
  }

type FV = FreeVar () Lifted.Expr

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
  SLambda.Lam {} -> internalError "liftExpr Lam"
  SLambda.ExternCode c retType -> Lifted.ExternCode <$> mapM liftAnnoExpr c <*> liftExpr retType

liftAnnoExpr
  :: Anno SLambda.Expr FV
  -> LambdaLift (Anno Lifted.Expr FV)
liftAnnoExpr (Anno e t) = Anno <$> liftExpr e <*> liftExpr t

liftLambda
  :: Telescope () SLambda.Expr FV
  -> AnnoScope TeleVar SLambda.Expr FV
  -> LambdaLift (Lifted.Expr FV)
liftLambda tele lamScope = do
  logFreeVar 20 "liftLambda" $ Sized.Function tele lamScope

  let sortedFvs = topoSortVars $ toHashSet tele <> toHashSet lamScope

  (params, lamBody) <- closeLambda tele lamScope sortedFvs

  let args = (\v -> Anno (pure v) (varType v)) <$> sortedFvs
      addArgs | null args = id
              | otherwise = (`Lifted.Call` args)

  let fun = Sized.functionTyped params lamBody
  logFreeVar 20 "liftLambda result" fun

  g <- liftThing $ close (error "liftLambda not closed") fun

  return $ addArgs $ global g

closeLambda
  :: Telescope () SLambda.Expr FV
  -> AnnoScope TeleVar SLambda.Expr FV
  -> Vector FV
  -> LambdaLift (Vector FV, Anno Lifted.Expr FV)
closeLambda tele lamScope sortedFvs = do
  vs <- forTeleWithPrefixM tele $ \h () s vs -> do
    let e = instantiateTele pure vs s
    e' <- liftExpr e
    freeVar h () e'

  let lamExpr = instantiateAnnoTele pure vs lamScope
  lamExpr' <- liftAnnoExpr lamExpr

  return (sortedFvs <> vs, lamExpr')

topoSortVars
  :: HashSet FV
  -> Vector FV
topoSortVars vs
  = Vector.fromList
  $ fmap acyclic
  $ topoSortWith id (toHashSet . varType)
  $ HashSet.toList vs
  where
    acyclic (AcyclicSCC a) = a
    acyclic (CyclicSCC _) = error "topoSortVars"

liftLet
  :: LetRec SLambda.Expr FV
  -> Scope LetVar SLambda.Expr FV
  -> LambdaLift (Lifted.Expr FV)
liftLet ds scope = do
  vs <- forMLet ds $ \h _ t -> do
    t' <- liftExpr t
    freeVar h () t'

  let instantiatedDs = Vector.zip vs $ instantiateLet pure vs <$> letBodies ds
      dsToLift = [(v, body) | (v, body@(SLambda.lamView -> Just _)) <- toList instantiatedDs]
      liftedVars = toHashSet $ fst <$> dsToLift
      fvs = fold (toHashSet . snd <$> dsToLift) `HashSet.difference` liftedVars
      sortedFvs = topoSortVars fvs
      args = (\v -> Anno (pure v) (varType v)) <$> sortedFvs
      addArgs | null args = id
              | otherwise = (`Lifted.Call` args)

  subVec <- forM (toVector dsToLift) $ \(v, _) -> do
    g <- fromNameHint freshName freshNameWithHint $ varHint v
    return (v, g)

  logShow 20 "subVec" subVec
  logShow 20 "sortedFvs" fvs

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
              Nothing -> error "liftLet g"
        (params, lamBody) <- closeLambda (subBound lamTele) (subBound lamScope) sortedFvs
        liftNamedThing g $ close (error "liftLet not closed") $ Sized.functionTyped params lamBody
        return $ addArgs $ global g
      _ -> liftExpr $ subBind body

  letBody <- liftExpr (subBind $ instantiateLet pure vs scope)

  let sortedDs = topoSortWith fst (toHashSet . snd) (Vector.zip vs liftedDs)

  return $ lets sortedDs letBody

liftBranches
  :: Branches () SLambda.Expr FV
  -> LambdaLift (Branches () Lifted.Expr FV)
liftBranches (ConBranches cbrs) = fmap ConBranches $
  forM cbrs $ \(ConBranch qc tele brScope) -> do
    vs <- forTeleWithPrefixM tele $ \h () s vs -> do
      let e = instantiateTele pure vs s
      e' <- liftExpr e
      freeVar h () e'
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
    go _ = error "Circular Lift lets"

liftToDefinitionM
  :: Closed (Anno SLambda.Expr)
  -> LambdaLift (Closed (Sized.Definition Lifted.Expr))
liftToDefinitionM (Closed (Anno (SLambda.Lams tele bodyScope) _)) = do
  vs <- forTeleWithPrefixM tele $ \h () s vs -> do
    let e = instantiateTele pure vs s
    e' <- liftExpr e
    freeVar h () e'
  let body = instantiateAnnoTele pure vs bodyScope
  body' <- liftAnnoExpr body
  return
    $ close (error "liftToDefinitionM")
    $ Sized.FunctionDef Public Sized.NonClosure
    $ Sized.functionTyped vs body'
liftToDefinitionM (Closed sexpr) = do
  sexpr' <- liftAnnoExpr sexpr
  logFreeVar 20 "liftToDefinitionM sexpr'" sexpr'
  return
    $ close (error "liftToDefinitionM 2")
    $ Sized.ConstantDef Public
    $ Sized.Constant sexpr'

liftToDefinition
  :: QName
  -> Closed (Anno SLambda.Expr)
  -> VIX (Closed (Sized.Definition Lifted.Expr), [(QName, Closed (Sized.Function Lifted.Expr))])
liftToDefinition (QName mname name) expr
  = runLift (QName mname $ name <> "-lifted") (liftToDefinitionM expr)
