{-# LANGUAGE FlexibleContexts, MonadComprehensions, OverloadedStrings #-}
module Frontend.ScopeCheck where

import Control.Monad.RWS
import Control.Monad.Except
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Lazy(HashMap)
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Vector as Vector
import Data.Void

import Syntax
import Syntax.Concrete.Pattern
import qualified Syntax.Concrete.Scoped as Scoped
import qualified Syntax.Concrete.Unscoped as Unscoped
import Util
import Util.TopoSort
import VIX

data ScopeEnv = ScopeEnv
  { scopeConstrTypes :: Constr -> HashSet QName -- TODO could be just bool?
  }

type ScopeCheck = RWS ScopeEnv () (HashSet QName)

runScopeCheck :: ScopeCheck a -> ScopeEnv -> (a, HashSet QName)
runScopeCheck m env = (a, s)
  where
    (a, s, ~()) = runRWS m env mempty

scopeCheckModule
  :: Module (HashMap QName (SourceLoc, Unscoped.Definition QName, Unscoped.Type QName))
  -> VIX [[(QName, SourceLoc, Scoped.PatDefinition Scoped.Expr Void, Scoped.Type Void)]]
scopeCheckModule modul = do
  context <- gets vixContext

  let env = ScopeEnv lookupConstr
      lookupConstr c = HashMap.lookupDefault mempty c constrs
      constrs = multiUnions $
        [ HashMap.singleton c $ HashSet.singleton n
        | (n, (_, Unscoped.DataDefinition _ d, _)) <- HashMap.toList $ moduleContents modul
        , c <- constrName <$> d
        ] <>
        [ HashMap.singleton c $ HashSet.singleton n
        | (n, (DataDefinition d _, _)) <- HashMap.toList context
        , c <- constrNames d
        ]

      checkedDefDeps = for (HashMap.toList $ moduleContents modul) $ \(n, (loc, def, typ)) -> do
        let (def', ddeps) = runScopeCheck (scopeCheckDefinition def) env
            (typ', tdeps) = runScopeCheck (scopeCheckExpr typ) env
        (n, (loc, def', typ'), toHashSet def' <> toHashSet typ' <> ddeps <> tdeps)

      defDeps = for checkedDefDeps $ \(n, _, deps) -> (n, deps)
      checkedDefs = for checkedDefDeps $ \(n, def, _) -> (n, def)

  otherNames <- gets vixModuleNames

  let localNames = HashMap.keys $ moduleContents modul
      localAliases = HashMap.fromList
        [ (unqualified $ qnameName qn, HashSet.singleton qn)
        | qn <- localNames
        ]
      imports = Import "Sixten.Builtin" "Sixten.Builtin" AllExposed : moduleImports modul
      aliases = multiUnions $ localAliases : (importedAliases otherNames <$> imports)
      lookupAlias qname
        | HashSet.size candidates == 1 = return $ head $ HashSet.toList candidates
        | otherwise = throwError $ "scopeCheckProgram ambiguous " ++ show candidates
        where
          candidates = HashMap.lookupDefault (HashSet.singleton qname) qname aliases

  resolvedDefs <- forM checkedDefs $ \(n, (loc, def, typ)) -> do
    def' <- traverse lookupAlias def
    typ' <- traverse lookupAlias typ
    return (n, (loc, bound global global def', bind global global typ'))

  resolvedDefDeps <- forM defDeps $ \(n, deps) -> do
    deps' <- traverse lookupAlias $ HashSet.toList deps
    return (n, HashSet.fromList deps')

  let resolvedDefsMap = HashMap.fromList resolvedDefs
      sortedDeps = topoSort resolvedDefDeps
  return $ for sortedDeps $ \ns -> for ns $ \n -> do
    let (loc, def, typ) = resolvedDefsMap HashMap.! n
    (n, loc, def, typ)

  where
    for = flip map

scopeCheckDefinition
  :: Unscoped.Definition QName
  -> ScopeCheck (Scoped.PatDefinition Scoped.Expr QName)
scopeCheckDefinition (Unscoped.Definition clauses) =
  Scoped.PatDefinition <$> mapM scopeCheckClause clauses
scopeCheckDefinition (Unscoped.DataDefinition params cs) = do
  let paramNames = (\(_, n, _) -> unqualified n) <$> params
      abstr = abstract $ teleAbstraction $ Vector.fromList paramNames
  Scoped.PatDataDefinition . DataDef <$> mapM (mapM (fmap abstr . scopeCheckExpr)) cs

scopeCheckClause
  :: Unscoped.Clause QName
  -> ScopeCheck (Scoped.Clause Scoped.Expr QName)
scopeCheckClause (Unscoped.Clause plicitPats e) = do
  plicitPats' <- traverse (traverse scopeCheckPat) plicitPats

  let pats = snd <$> plicitPats'
      vars = join (toVector <$> pats)
      typedPats'' = second void <$> abstractPatternsTypes vars plicitPats'

  Scoped.Clause typedPats'' . abstract (patternAbstraction vars) <$> scopeCheckExpr e

scopeCheckExpr
  :: Unscoped.Expr QName
  -> ScopeCheck (Scoped.Expr QName)
scopeCheckExpr expr = case expr of
  Unscoped.Var n | Just v <- isUnqualified n -> do -- TODO qualified constructors
    let c = fromName v
    defs <- asks (($ c) . scopeConstrTypes)
    if HashSet.null defs then
      return $ Scoped.Var n
    else do
      modify $ mappend defs
      return $ Scoped.Con $ Left c
  Unscoped.Var v -> return $ Scoped.Var v
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
  Unscoped.ExternCode c -> Scoped.ExternCode <$> mapM scopeCheckExpr c
  Unscoped.Wildcard -> return Scoped.Wildcard
  Unscoped.SourceLoc loc e -> Scoped.SourceLoc loc <$> scopeCheckExpr e

scopeCheckBranch
  :: Pat (Unscoped.Expr QName) QName
  -> Unscoped.Expr QName
  -> ScopeCheck (Pat (PatternScope Scoped.Expr QName) (), PatternScope Scoped.Expr QName)
scopeCheckBranch pat e = do
  pat' <- scopeCheckPat pat
  let vs = toVector pat'
  (,) (void $ abstractPatternTypes vs pat') . abstract (patternAbstraction vs) <$> scopeCheckExpr e

scopeCheckPat
  :: Pat (Unscoped.Expr QName) QName
  -> ScopeCheck (Pat (Scoped.Expr QName) QName)
scopeCheckPat pat = case pat of
  VarPat h n | Just v <- isUnqualified n -> do -- TODO qualified constructors
    let c = fromName v
    defs <- asks (($ c) . scopeConstrTypes)
    if HashSet.null defs then
      return $ VarPat h n
    else do
      modify $ mappend defs
      return $ ConPat (Left c) mempty
  VarPat h v -> return $ VarPat h v
  WildcardPat -> return WildcardPat
  LitPat l -> return $ LitPat l
  ConPat con ps -> do
    case con of
      Left c -> do
        defs <- asks (($ c) . scopeConstrTypes)
        modify $ mappend defs
      Right (QConstr n _) -> -- TODO aliases
        modify $ HashSet.insert n
    ConPat con <$> mapM (\(p, pat') -> (,) p <$> scopeCheckPat pat') ps
  AnnoPat t p -> AnnoPat <$> scopeCheckExpr t <*> scopeCheckPat p
  ViewPat t p -> ViewPat <$> scopeCheckExpr t <*> scopeCheckPat p
  PatLoc loc p -> PatLoc loc <$> scopeCheckPat p
