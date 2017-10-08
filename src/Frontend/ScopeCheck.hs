{-# LANGUAGE FlexibleContexts, MonadComprehensions, OverloadedStrings #-}
module Frontend.ScopeCheck where

import Control.Monad.Except
import Control.Monad.RWS
import Data.Bifunctor
import Data.Bitraversable
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Lazy(HashMap)
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.Maybe
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Syntax
import Syntax.Concrete.Pattern
import qualified Syntax.Concrete.Scoped as Scoped
import qualified Syntax.Concrete.Unscoped as Unscoped
import Util
import Util.TopoSort
import VIX

newtype ScopeEnv = ScopeEnv
  { scopeConstrs :: QName -> HashSet QConstr
  }

type ScopeCheck = RWS ScopeEnv () (HashSet QName)

runScopeCheck :: ScopeCheck a -> ScopeEnv -> (a, HashSet QName)
runScopeCheck m env = (a, s)
  where
    (a, s, ~()) = runRWS m env mempty

scopeCheckModule
  :: Module (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition QName))
  -> VIX [[(QName, SourceLoc, Scoped.TopLevelPatDefinition Scoped.Expr void, Scoped.Type void)]]
scopeCheckModule modul = do
  otherNames <- gets vixModuleNames

  let env = ScopeEnv lookupConstr
      lookupConstr c = HashMap.lookupDefault mempty c constrs
      constrs = multiFromList
        [ (QName mempty $ fromConstr c, QConstr n c)
        | (n, (_, Unscoped.TopLevelDataDefinition _ _ d)) <- HashMap.toList $ moduleContents modul
        , c <- constrName <$> d
        ] `multiUnion`
        importedConstrAliases
      imports = Import Builtin.BuiltinModuleName Builtin.BuiltinModuleName AllExposed : moduleImports modul
      importAliases = multiUnions $ importedAliases otherNames <$> imports

      checkedDefDeps = for (HashMap.toList $ moduleContents modul) $ \(n, (loc, def)) -> do
        let ((def', typ'), deps) = runScopeCheck (scopeCheckTopLevelDefinition def) env
        (n, (loc, def', typ'), toHashSet def' <> toHashSet typ' <> deps)

      defDeps = for checkedDefDeps $ \(n, _, deps) -> (n, deps)
      checkedDefs = for checkedDefDeps $ \(n, def, _) -> (n, def)

      importedNameAliases = multiMapMaybe (either (const Nothing) Just) importAliases
      importedConstrAliases = multiMapMaybe (either Just $ const Nothing) importAliases

      localNames = HashMap.keys $ moduleContents modul
      localAliases = multiFromList
        [ (unqualified $ qnameName qn, qn)
        | qn <- localNames
        ] `multiUnion` localMethods
      localMethods = multiFromList
        [ (QName mempty m, QName modName m)
        | (m, QName modName _) <- methodClasses
        ]

      aliases = localAliases `multiUnion` importedNameAliases
      lookupAlias qname
        | HashSet.size candidates == 1 = return $ head $ HashSet.toList candidates
        | otherwise = throwError $ "scopeCheckModule ambiguous " ++ show candidates
        where
          candidates = HashMap.lookupDefault (HashSet.singleton qname) qname aliases

      methodClasses =
        [ (m, n)
        | (n, (_, Unscoped.TopLevelClassDefinition _ _ ms)) <- HashMap.toList $ moduleContents modul
        , m <- methodName <$> ms
        ]
      methodDeps = multiFromList [(QName mempty m, n) | (m, n) <- methodClasses]
      depAliases = aliases `multiUnion` methodDeps
      lookupAliasDep qname = HashMap.lookupDefault (HashSet.singleton qname) qname depAliases

  resolvedDefs <- forM checkedDefs $ \(n, (loc, def, typ)) -> do
    def' <- traverse lookupAlias def
    typ' <- traverse lookupAlias typ
    return (n, (loc, bound global global def', bind global global typ'))

  let resolvedDefDeps = for defDeps $ \(n, deps) -> do
        let deps' = lookupAliasDep <$> HashSet.toList deps
        (n, HashSet.unions deps')

  let resolvedDefsMap = HashMap.fromList resolvedDefs
      -- TODO use topoSortWith
      sortedDeps = topoSort resolvedDefDeps
  return $ for sortedDeps $ \ns -> for ns $ \n -> do
    let (loc, def, typ) = resolvedDefsMap HashMap.! n
    (n, loc, def, typ)

  where
    for = flip map

scopeCheckTopLevelDefinition
  :: Unscoped.TopLevelDefinition QName
  -> ScopeCheck (Scoped.TopLevelPatDefinition Scoped.Expr QName, Scoped.Type QName)
scopeCheckTopLevelDefinition (Unscoped.TopLevelDefinition d) =
  first Scoped.TopLevelPatDefinition . snd <$> scopeCheckDefinition d
scopeCheckTopLevelDefinition (Unscoped.TopLevelDataDefinition _name params cs) = do
  (typ, abstr) <- scopeCheckParamsType params $ pure Builtin.TypeName
  cs' <- mapM (mapM (fmap abstr . scopeCheckExpr)) cs
  let res = Scoped.TopLevelPatDataDefinition $ DataDef cs'
  return (res, typ)
scopeCheckTopLevelDefinition (Unscoped.TopLevelClassDefinition _name params ms) = do
  (typ, abstr) <- scopeCheckParamsType params $ pure Builtin.TypeName -- TODO: Should this be a constraint?
  ms' <- mapM (mapM (fmap abstr . scopeCheckExpr)) ms
  let res = Scoped.TopLevelPatClassDefinition $ ClassDef ms'
  return (res, typ)
scopeCheckTopLevelDefinition (Unscoped.TopLevelInstanceDefinition typ ms) = do
  typ' <- scopeCheckExpr typ
  ms' <- mapM (\(loc, m) -> (,) loc <$> scopeCheckDefinition m) ms
  let res = Scoped.TopLevelPatInstanceDefinition
        $ Scoped.PatInstanceDef
        $ Vector.fromList
        $ (\(loc, (n, (d, _typ))) -> (n, loc, d)) -- TODO use the type
        <$> ms'
  return (res, typ')

scopeCheckParamsType
  :: Monad f
  => [(Plicitness, Name, Unscoped.Type QName)]
  -> Unscoped.Expr QName
  -> ScopeCheck (Scoped.Expr QName, f QName -> Scope TeleVar f QName)
scopeCheckParamsType params kind = do
  typ' <- scopeCheckExpr typ
  return (typ', abstr)
  where
    pats = (\(p, n, t) -> (p, AnnoPat t $ VarPat (nameHint n) $ unqualified n)) <$> params
    typ = Unscoped.pis pats kind
    paramNames = (\(_, n, _) -> unqualified n) <$> params
    abstr = abstract $ teleAbstraction $ Vector.fromList paramNames

scopeCheckDefinition
  :: Unscoped.Definition Unscoped.Expr QName
  -> ScopeCheck (Name, (Scoped.PatDefinition (Scoped.Clause void Scoped.Expr QName), Scoped.Type QName))
scopeCheckDefinition (Unscoped.Definition name a clauses mtyp) = do
  res <- Scoped.PatDefinition a IsOrdinaryDefinition <$> mapM scopeCheckClause clauses
  typ <- scopeCheckExpr $ fromMaybe Unscoped.Wildcard mtyp
  return (name, (res, typ))

scopeCheckClause
  :: Unscoped.Clause Unscoped.Expr QName
  -> ScopeCheck (Scoped.Clause void Scoped.Expr QName)
scopeCheckClause (Unscoped.Clause plicitPats e) = do
  plicitPats' <- traverse (traverse scopeCheckPat) plicitPats

  let pats = snd <$> plicitPats'
      vars = join (toVector <$> pats)
      typedPats'' = second (void . first (mapBound B)) <$> abstractPatternsTypes vars plicitPats'

  Scoped.Clause typedPats'' . abstract (fmap B . patternAbstraction vars) <$> scopeCheckExpr e

scopeCheckExpr
  :: Unscoped.Expr QName
  -> ScopeCheck (Scoped.Expr QName)
scopeCheckExpr expr = case expr of
  Unscoped.Var v -> do
    constrCandidates <- asks (($ v) . scopeConstrs)
    if HashSet.null constrCandidates then
      return $ Scoped.Var v
    else do
      let defs = HashSet.map qconstrTypeName constrCandidates
      modify $ mappend defs
      return $ Scoped.Con constrCandidates
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
  Unscoped.Let defs body -> do
    defs' <- traverse (bitraverse pure scopeCheckDefinition) defs
    body' <- scopeCheckExpr body
    let sortedDefs = topoSortWith
          (\(_, (name, _)) -> fromName name)
          (\(_, (_, (d, t))) -> foldMap toHashSet d <> toHashSet t)
          defs'

        go ds e = do
          let ds' = Vector.fromList ds
              abstr = letAbstraction $ fromName . fst . snd <$> ds'
          Scoped.Let
            ((\(loc, (name, (def, typ))) -> (loc, fromName name, Scoped.abstractClause abstr <$> def, abstract abstr typ)) <$> ds')
            (abstract abstr e)

    return $ foldr go body' sortedDefs
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
  VarPat h v -> do
    constrCandidates <- asks (($ v) . scopeConstrs)
    if HashSet.null constrCandidates then
      return $ VarPat h v
    else do
      modify $ mappend $ HashSet.map qconstrTypeName constrCandidates
      return $ ConPat constrCandidates mempty
  WildcardPat -> return WildcardPat
  LitPat l -> return $ LitPat l
  ConPat cons ps -> do
    conss <- forM (HashSet.toList cons) $ \(QConstr (QName mname _tname) cname) -> do
      let qconName = QName mname $ fromConstr cname
      constrCandidates <- asks (($ qconName) . scopeConstrs)
      forM_ constrCandidates $ \(QConstr def _) -> modify $ HashSet.insert def
      return constrCandidates
    ConPat (HashSet.unions conss) <$> mapM (\(p, pat') -> (,) p <$> scopeCheckPat pat') ps
  AnnoPat t p -> AnnoPat <$> scopeCheckExpr t <*> scopeCheckPat p
  ViewPat t p -> ViewPat <$> scopeCheckExpr t <*> scopeCheckPat p
  PatLoc loc p -> PatLoc loc <$> scopeCheckPat p
