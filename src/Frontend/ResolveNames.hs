{-# LANGUAGE FlexibleContexts, MonadComprehensions, OverloadedStrings #-}
module Frontend.ResolveNames where

import Control.Monad.Except
import Control.Monad.RWS
import Data.Bifunctor
import Data.Bitraversable
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Lazy(HashMap)
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import qualified Frontend.Declassify as Declassify
import Syntax
import Syntax.Concrete.Pattern
import qualified Syntax.Concrete.Scoped as Scoped
import qualified Syntax.Concrete.Unscoped as Unscoped
import Util
import Util.MultiHashMap(MultiHashMap)
import qualified Util.MultiHashMap as MultiHashMap
import Util.TopoSort
import VIX

newtype Env = Env
  { scopeConstrs :: QName -> HashSet QConstr
  }

type ResolveNames = RWST Env () (HashSet QName) VIX

runResolveNames :: ResolveNames a -> Env -> VIX (a, HashSet QName)
runResolveNames m env = do
  (a, s, ~()) <- runRWST m env mempty
  return (a, s)

-- TODO use plain Name for unresolved names
resolveModule
  :: Module (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition))
  -> VIX [[(QName, SourceLoc, Scoped.TopLevelPatDefinition Scoped.Expr void, Maybe (Scoped.Type void))]]
resolveModule modul = do
  let imports
        = Import Builtin.BuiltinModuleName Builtin.BuiltinModuleName AllExposed
        : moduleImports modul

  (importedConstrAliases, importedNameAliases) <- mconcat <$> mapM importedAliases imports
  let env = Env
        $ flip MultiHashMap.lookup
        $ localConstrAliases (moduleContents modul) <> importedConstrAliases

  checkedDefDeps <- forM (HashMap.toList $ moduleContents modul) $ \(n, (loc, def)) -> do
    ((def', mtyp'), deps) <- runResolveNames (resolveTopLevelDefinition def) env
    return (n, (loc, def', mtyp'), toHashSet def' <> foldMap toHashSet mtyp' <> deps)

  let aliases = localAliases (moduleContents modul) <> importedNameAliases
      lookupAlias qname
        | HashSet.size candidates == 1 = return $ head $ HashSet.toList candidates
        -- TODO: Error message, duplicate checking, tests
        | otherwise = throwError $ TypeError ("resolveModule ambiguous" PP.<+> shower candidates) Nothing mempty
        where
          candidates = MultiHashMap.lookupDefault (HashSet.singleton qname) qname aliases

  resolvedDefs <- forM checkedDefDeps $ \(n, (loc, def, mtyp), deps) -> do
    def' <- traverse lookupAlias def
    mtyp' <- traverse (traverse lookupAlias) mtyp
    return (n, (loc, def' >>>= global, (>>= global) <$> mtyp'), deps)

  -- Each _usage_ of a class (potentially) depends on all its instances.
  -- But the class itself doesn't (necessarily).
  --
  -- So, create an instanceDeps table: For each definition that's an instance i of
  -- class c, add a vertex c -> i, and map the instanceDeps table over all _dependencies_.
  instanceDeps <- instances resolvedDefs
  let depAliases = aliases <> methodClasses (moduleContents modul)
      lookupAliasDep qname = MultiHashMap.lookupDefault (HashSet.singleton qname) qname depAliases
      addInstanceDeps dep = HashSet.insert dep $ MultiHashMap.lookup dep instanceDeps
      addExtraDeps deps = do
        let deps' = lookupAliasDep <$> HashSet.toList deps
            deps'' = addInstanceDeps <$> HashSet.toList (mconcat deps')
        mconcat deps''

  let sortedDefGroups = flattenSCC <$> topoSortWith fst3 (addExtraDeps . thd3) resolvedDefs

  return [[(n, loc, def, typ) | (n, (loc, def, typ), _) <- defs] | defs <- sortedDefGroups]

localConstrAliases
  :: HashMap QName (SourceLoc, Unscoped.TopLevelDefinition)
  -> MultiHashMap QName QConstr
localConstrAliases contents = MultiHashMap.fromList
  [ (QName mempty $ fromConstr c, QConstr n c)
  | (n, (_, Unscoped.TopLevelDataDefinition _ _ d)) <- HashMap.toList contents
  , c <- constrName <$> d
  ]

localAliases
  :: HashMap QName (SourceLoc, Unscoped.TopLevelDefinition)
  -> MultiHashMap QName QName
localAliases contents = MultiHashMap.fromList
  [ (unqualified $ qnameName qn, qn)
  | qn <- HashMap.keys contents
  ] <> localMethods
  where
    localMethods
      = MultiHashMap.mapWithKey
        (\(QName _ m) (QName modName _) -> QName modName m)
        $ methodClasses contents

methodClasses
  :: HashMap QName (SourceLoc, Unscoped.TopLevelDefinition)
  -> MultiHashMap QName QName
methodClasses contents = MultiHashMap.fromList
  [ (unqualified m, n)
  | (n, (_, Unscoped.TopLevelClassDefinition _ _ ms)) <- HashMap.toList contents
  , m <- methodName <$> ms
  ]

instances
  :: [(QName, (SourceLoc, Scoped.TopLevelPatDefinition Scoped.Expr void, Maybe (Scoped.Expr void)), a)]
  -> VIX (MultiHashMap QName QName)
instances defs = fmap (MultiHashMap.fromList . concat) $ forM defs $ \(name, (_, def, mtyp), _) -> case (def, mtyp) of
  (Scoped.TopLevelPatInstanceDefinition _, Just typ) -> do
    c <- Declassify.getClass typ
    return [(c, name)]
  _ -> return mempty

-- TODO add test for imports of empty modules
importedAliases
  :: Import
  -> VIX (MultiHashMap QName QConstr, MultiHashMap QName QName)
importedAliases (Import modName asName exposed) = do
  otherConstrs <- liftVIX $ gets vixModuleConstrs
  otherNames <- liftVIX $ gets vixModuleNames
  let
    constrs
      = MultiHashMap.fromList
      $ fmap (\c -> (fromConstr $ qconstrConstr c, c))
      $ HashSet.toList
      $ MultiHashMap.lookup modName otherConstrs

    names
      = MultiHashMap.fromList
      $ fmap (\n -> (qnameName n, n))
      $ HashSet.toList
      $ MultiHashMap.lookup modName otherNames

    exposedConstrs = case exposed of
      AllExposed -> constrs
      Exposed ns -> MultiHashMap.setIntersection constrs ns

    exposedNames = case exposed of
      AllExposed -> names
      Exposed ns -> MultiHashMap.setIntersection names ns

  return
    ( MultiHashMap.mapKeys unqualified exposedConstrs <> MultiHashMap.mapKeys (QName asName) constrs
    , MultiHashMap.mapKeys unqualified exposedNames <> MultiHashMap.mapKeys (QName asName) names
    )

-- | Distinguish variables from constructors, resolve scopes
resolveTopLevelDefinition
  :: Unscoped.TopLevelDefinition
  -> ResolveNames (Scoped.TopLevelPatDefinition Scoped.Expr QName, Maybe (Scoped.Type QName))
resolveTopLevelDefinition (Unscoped.TopLevelDefinition d) =
  first Scoped.TopLevelPatDefinition . snd <$> resolveDefinition d
resolveTopLevelDefinition (Unscoped.TopLevelDataDefinition _name params cs) = do
  (typ, abstr) <- resolveParamsType params $ Unscoped.Var Builtin.TypeName
  cs' <- mapM (mapM (fmap abstr . resolveExpr)) cs
  let res = Scoped.TopLevelPatDataDefinition $ DataDef cs'
  return (res, Just typ)
resolveTopLevelDefinition (Unscoped.TopLevelClassDefinition _name params ms) = do
  (typ, abstr) <- resolveParamsType params $ Unscoped.Var Builtin.TypeName
  ms' <- mapM (mapM (fmap abstr . resolveExpr)) ms
  let res = Scoped.TopLevelPatClassDefinition $ ClassDef ms'
  return (res, Just typ)
resolveTopLevelDefinition (Unscoped.TopLevelInstanceDefinition typ ms) = do
  typ' <- resolveExpr typ
  ms' <- mapM (\(loc, m) -> (,) loc <$> resolveDefinition m) ms
  let res = Scoped.TopLevelPatInstanceDefinition
        $ Scoped.PatInstanceDef
        $ Vector.fromList
        $ (\(loc, (n, (d, mtyp))) -> (n, loc, d, mtyp))
        <$> ms'
  return (res, Just typ')

resolveParamsType
  :: Monad f
  => [(Plicitness, Name, Unscoped.Type)]
  -> Unscoped.Expr
  -> ResolveNames (Scoped.Expr QName, f QName -> Scope TeleVar f QName)
resolveParamsType params kind = do
  typ' <- resolveExpr typ
  return (typ', abstr)
  where
    pats = (\(p, n, t) -> (p, AnnoPat (VarPat (NameHint n) $ unqualified n) t)) <$> params
    typ = Unscoped.pis pats kind
    paramNames = (\(_, n, _) -> unqualified n) <$> params
    abstr = abstract $ teleAbstraction $ Vector.fromList paramNames

resolveDefinition
  :: Unscoped.Definition Unscoped.Expr
  -> ResolveNames (Name, (Scoped.PatDefinition (Scoped.Clause void Scoped.Expr QName), Maybe (Scoped.Type QName)))
resolveDefinition (Unscoped.Definition name a clauses mtyp) = do
  res <- Scoped.PatDefinition a IsOrdinaryDefinition <$> mapM resolveClause clauses
  mtyp' <- forM mtyp resolveExpr
  return (name, (res, mtyp'))

resolveClause
  :: Unscoped.Clause Unscoped.Expr
  -> ResolveNames (Scoped.Clause void Scoped.Expr QName)
resolveClause (Unscoped.Clause plicitPats e) = do
  plicitPats' <- traverse (traverse resolvePat) plicitPats

  let pats = snd <$> plicitPats'
      vars = join (toVector <$> pats)
      typedPats'' = second (void . first (mapBound B)) <$> abstractPatternsTypes vars plicitPats'

  Scoped.Clause typedPats'' . abstract (fmap B . patternAbstraction vars) <$> resolveExpr e

resolveExpr
  :: Unscoped.Expr
  -> ResolveNames (Scoped.Expr QName)
resolveExpr expr = case expr of
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
    pat' <- resolvePat pat
    let vs = toVector pat'
    Scoped.Pi p (void $ abstractPatternTypes vs pat')
      . abstract (patternAbstraction vs) <$> resolveExpr e
  Unscoped.Lam p pat e -> do
    pat' <- resolvePat pat
    let vs = toVector pat'
    Scoped.Lam p (void $ abstractPatternTypes vs pat')
      . abstract (patternAbstraction vs) <$> resolveExpr e
  Unscoped.App e1 p e2 -> Scoped.App
    <$> resolveExpr e1
    <*> pure p
    <*> resolveExpr e2
  Unscoped.Let defs body -> do
    defs' <- traverse (bitraverse pure resolveDefinition) defs
    body' <- resolveExpr body
    let sortedDefs = topoSortWith
          (\(_, (name, _)) -> fromName name)
          (\(_, (_, (d, mt))) -> foldMap toHashSet d <> foldMap toHashSet mt)
          defs'

        go ds e = do
          let ds' = Vector.fromList ds
              abstr = letAbstraction $ fromName . fst . snd <$> ds'
          Scoped.Let
            ((\(loc, (name, (def, mtyp))) -> (loc, fromName name, Scoped.abstractClause abstr <$> def, abstract abstr <$> mtyp)) <$> ds')
            (abstract abstr e)

    return $ foldr go body' $ flattenSCC <$> sortedDefs
  Unscoped.Case e pats -> Scoped.Case
    <$> resolveExpr e
    <*> mapM (uncurry resolveBranch) pats
  Unscoped.ExternCode c -> Scoped.ExternCode <$> mapM resolveExpr c
  Unscoped.Wildcard -> return Scoped.Wildcard
  Unscoped.SourceLoc loc e -> Scoped.SourceLoc loc <$> resolveExpr e

resolveBranch
  :: Pat Unscoped.Expr QName
  -> Unscoped.Expr
  -> ResolveNames (Pat (PatternScope Scoped.Expr QName) (), PatternScope Scoped.Expr QName)
resolveBranch pat e = do
  pat' <- resolvePat pat
  let vs = toVector pat'
  (,) (void $ abstractPatternTypes vs pat') . abstract (patternAbstraction vs) <$> resolveExpr e

resolvePat
  :: Pat Unscoped.Expr QName
  -> ResolveNames (Pat (Scoped.Expr QName) QName)
resolvePat pat = case pat of
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
    ConPat (mconcat conss) <$> mapM (\(p, pat') -> (,) p <$> resolvePat pat') ps
  AnnoPat p t -> AnnoPat <$> resolvePat p <*> resolveExpr t
  ViewPat t p -> ViewPat <$> resolveExpr t <*> resolvePat p
  PatLoc loc p -> PatLoc loc <$> resolvePat p
