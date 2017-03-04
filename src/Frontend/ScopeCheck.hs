{-# LANGUAGE MonadComprehensions #-}
module Frontend.ScopeCheck where

import Control.Monad.RWS
import Data.Bifunctor
import Data.Foldable
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Lazy(HashMap)
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Vector as Vector
import Data.Void

import qualified Builtin
import Syntax
import Syntax.Concrete.Pattern
import qualified Syntax.Concrete.Scoped as Scoped
import qualified Syntax.Concrete.Unscoped as Unscoped
import TopoSort
import Util

type ScopeCheck = RWS (Constr -> HashSet Name) () (HashSet Name)

runScopeCheck :: ScopeCheck a -> (Constr -> HashSet Name) -> (a, HashSet Name)
runScopeCheck m constrDefs = (a, s)
  where
    (a, s, ~()) = runRWS m constrDefs mempty

scopeCheckProgram
  :: HashMap Name (SourceLoc, Unscoped.Definition Name, Unscoped.Type Name)
  -> [[(Name, SourceLoc, Scoped.PatDefinition Scoped.Expr Void, Scoped.Type Void)]]
scopeCheckProgram defs = do
  let checkedDefDeps = for (HashMap.toList defs) $ \(n, (loc, def, typ)) -> do
        let (def', defDeps) = runScopeCheck (scopeCheckDefinition def) lookupConstr
            (typ', typDeps) = runScopeCheck (scopeCheckExpr typ) lookupConstr
        (n, (loc, def', typ'), toHashSet def' <> toHashSet typ' <> defDeps <> typDeps)
  let defDeps = for checkedDefDeps $ \(n, _, deps) -> (n, deps)
      checkedDefs = HashMap.fromList $ for checkedDefDeps $ \(n, def, _) -> (n, def)
  let sortedDeps = topoSort defDeps
  for sortedDeps $ \ns -> for ns $ \n -> do
    let (loc, def, typ) = checkedDefs HashMap.! n
    (n, loc, bound global global def, bind global global typ)
  where
    constrs = unions $
      [ HashMap.singleton c $ HashSet.singleton n
      | (n, (_, Unscoped.DataDefinition _ d, _)) <- HashMap.toList defs
      , c <- constrName <$> d
      ] <>
      [ HashMap.singleton c $ HashSet.singleton n
      | (n, (DataDefinition d _, _)) <- HashMap.toList Builtin.context
      , c <- constrNames d
      ]
    lookupConstr c = HashMap.lookupDefault mempty c constrs

    union = HashMap.unionWith HashSet.union
    unions = foldl' union mempty

    for = flip map

scopeCheckDefinition
  :: Unscoped.Definition Name
  -> ScopeCheck (Scoped.PatDefinition Scoped.Expr Name)
scopeCheckDefinition (Unscoped.Definition clauses) =
  Scoped.PatDefinition <$> mapM scopeCheckClause clauses
scopeCheckDefinition (Unscoped.DataDefinition params cs) = do
  let paramNames = (\(_, n, _) -> n) <$> params
      abstr = abstract $ teleAbstraction $ Vector.fromList paramNames
  Scoped.PatDataDefinition . DataDef <$> mapM (mapM (fmap abstr . scopeCheckExpr)) cs

scopeCheckClause
  :: Unscoped.Clause Name
  -> ScopeCheck (Scoped.Clause Scoped.Expr Name)
scopeCheckClause (Unscoped.Clause plicitPats e) = do
  plicitPats' <- traverse (traverse scopeCheckPat) plicitPats

  let pats = snd <$> plicitPats'
      vars = join $ toVector <$> pats
      typedPats'' = second void <$> abstractPatternsTypes vars plicitPats'

  Scoped.Clause typedPats'' . abstract (patternAbstraction vars) <$> scopeCheckExpr e

scopeCheckExpr
  :: Unscoped.Expr Name
  -> ScopeCheck (Scoped.Expr Name)
scopeCheckExpr expr = case expr of
  Unscoped.Var v -> do
    let c = fromName v
    defs <- asks ($ c)
    if HashSet.null defs then
      return $ Scoped.Var v
    else do
      modify $ mappend defs
      return $ Scoped.Con $ Left c
  Unscoped.Global v -> return $ Scoped.Global v
  Unscoped.Lit l -> return $ Scoped.Lit l
  Unscoped.Pi p pat e -> do
    pat' <- scopeCheckPat pat
    let vs = toVector pat'
    Scoped.Pi p (void $ abstractPatternTypes vs pat')
      . abstract (patternAbstraction vs) <$> scopeCheckExpr e
  Unscoped.Lam p pat e -> do
    pat' <- scopeCheckPat pat
    let vs = toVector pat'
    Scoped.Lam p (void $ abstractPatternTypes vs pat')
      . abstract (patternAbstraction vs) <$> scopeCheckExpr e
  Unscoped.App e1 p e2 -> Scoped.App
    <$> scopeCheckExpr e1
    <*> pure p
    <*> scopeCheckExpr e2
  Unscoped.Case e pats -> Scoped.Case
    <$> scopeCheckExpr e
    <*> mapM (uncurry scopeCheckBranch) pats
  Unscoped.Wildcard -> return Scoped.Wildcard
  Unscoped.SourceLoc loc e -> Scoped.SourceLoc loc <$> scopeCheckExpr e

scopeCheckBranch
  :: Pat (Unscoped.Expr Name) Name
  -> Unscoped.Expr Name
  -> ScopeCheck (Pat (PatternScope Scoped.Expr Name) (), PatternScope Scoped.Expr Name)
scopeCheckBranch pat e = do
  pat' <- scopeCheckPat pat
  let vs = toVector pat'
  (,) (void $ abstractPatternTypes vs pat') . abstract (patternAbstraction vs) <$> scopeCheckExpr e

scopeCheckPat
  :: Pat (Unscoped.Expr Name) Name
  -> ScopeCheck (Pat (Scoped.Expr Name) Name)
scopeCheckPat pat = case pat of
  VarPat h v -> do
    let c = fromName v
    defs <- asks ($ c)
    if HashSet.null defs then
      return $ VarPat h v
    else do
      modify $ mappend defs
      return $ ConPat (Left c) mempty
  WildcardPat -> return WildcardPat
  LitPat l -> return $ LitPat l
  ConPat con ps -> do
    case con of
      Left c -> do
        defs <- asks ($ c)
        modify $ mappend defs
      Right (QConstr n _) ->
        modify $ HashSet.insert n
    ConPat con <$> mapM (\(p, pat') -> (,) p <$> scopeCheckPat pat') ps
  AnnoPat t p -> AnnoPat <$> scopeCheckExpr t <*> scopeCheckPat p
  ViewPat t p -> ViewPat <$> scopeCheckExpr t <*> scopeCheckPat p
  PatLoc loc p -> PatLoc loc <$> scopeCheckPat p
