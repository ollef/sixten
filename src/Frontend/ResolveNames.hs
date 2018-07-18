{-# LANGUAGE FlexibleContexts, MonadComprehensions, OverloadedStrings, ViewPatterns #-}
module Frontend.ResolveNames where

import Control.Monad.Except
import Control.Monad.RWS
import Data.Bitraversable
import Data.Foldable
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Lazy(HashMap)
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Pretty
import Syntax
import qualified Syntax.Pre.Literal as Literal
import Syntax.Pre.Pattern
import qualified Syntax.Pre.Scoped as Scoped
import qualified Syntax.Pre.Unscoped as Unscoped
import Util
import Util.MultiHashMap(MultiHashMap)
import qualified Util.MultiHashMap as MultiHashMap
import Util.TopoSort
import VIX hiding (instances)

newtype Env = Env
  { scopeConstrs :: PreName -> HashSet QConstr
  }

type ResolveNames = RWST Env () (HashSet QName) VIX

runResolveNames :: ResolveNames a -> Env -> VIX (a, HashSet QName)
runResolveNames m env = do
  (a, s, ~()) <- runRWST m env mempty
  return (a, s)

resolveModule
  :: Module (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition))
  -> VIX [[(QName, SourceLoc, Scoped.Definition Scoped.Expr void)]]
resolveModule modul = do
  let imports
        = Import Builtin.BuiltinModuleName Builtin.BuiltinModuleName AllExposed
        : moduleImports modul

  (importedConstrAliases, importedNameAliases) <- mconcat <$> mapM importedAliases imports
  let env = Env
        $ flip MultiHashMap.lookup
        $ localConstrAliases (moduleContents modul) <> importedConstrAliases

  checkedDefDeps <- forM (HashMap.toList $ moduleContents modul) $ \(n, (loc, def)) -> do
    (def', deps) <- runResolveNames (resolveTopLevelDefinition def) env
    return (n, loc, def', deps)

  let aliases = localAliases (moduleContents modul) <> importedNameAliases
      lookupAlias preName
        | HashSet.size candidates == 1 = return $ pure $ head $ HashSet.toList candidates
        | otherwise = do
          report
            $ TypeError ("Ambiguous name" PP.<+> red (pretty preName)) (preNameSourceLoc preName) $ PP.vcat
              [ "It could refer to" PP.<+> prettyHumanList "or" (dullBlue . pretty <$> toList candidates) <> "."
              ]
          (err, _) <- flip runResolveNames env $ resolveExpr $ Unscoped.App
            (Unscoped.Var $ fromQName Builtin.StaticErrorName)
            Explicit
            (Literal.string "error\n")
          return $ fromPreName <$> err
        where
          candidates = MultiHashMap.lookupDefault (HashSet.singleton $ fromPreName preName) preName aliases

  resolvedDefs <- forM checkedDefDeps $ \(n, loc, def, deps) -> do
    def' <- boundJoin <$> traverse lookupAlias def
    return (n, (loc, def' >>>= global), toHashSet def' <> deps)

  -- Each _usage_ of a class (potentially) depends on all its instances.
  -- But the class itself doesn't (necessarily).
  --
  -- So, create an instanceDeps table: For each definition that's an instance i of
  -- class c, add a vertex c -> i, and map the instanceDeps table over all _dependencies_.
  --
  -- We also add a dependency from method to class for all methods
  instanceDeps <- instances resolvedDefs
  let methodDeps = methodClasses $ moduleContents modul
      addMethodDeps dep
        = maybe (HashSet.singleton dep) (HashSet.insert dep . HashSet.singleton)
        $ HashMap.lookup dep methodDeps
      addInstanceDeps dep = HashSet.insert dep $ MultiHashMap.lookup dep instanceDeps
      addExtraDeps deps = do
        let deps' = mconcat $ addMethodDeps <$> HashSet.toList deps
            deps'' = addInstanceDeps <$> HashSet.toList deps'
        mconcat deps''

  let sortedDefGroups = flattenSCC <$> topoSortWith fst3 (addExtraDeps . thd3) resolvedDefs

  return [[(n, loc, def) | (n, (loc, def), _) <- defs] | defs <- sortedDefGroups]

localConstrAliases
  :: HashMap QName (SourceLoc, Unscoped.TopLevelDefinition)
  -> MultiHashMap PreName QConstr
localConstrAliases contents = MultiHashMap.fromList $ concat
  [ [ (k, QConstr n c)
    , (fromName (qnameName n) <> "." <> k, QConstr n c)
    , (fromModuleName (qnameModule n) <> "." <> k, QConstr n c)
    , (fromQName n <> "." <> k, QConstr n c)
    ]
  | (n, (_, Unscoped.TopLevelDataDefinition _ _ d)) <- HashMap.toList contents
  , c <- constrName <$> d
  , let k = fromConstr c
  ]

localAliases
  :: HashMap QName (SourceLoc, Unscoped.TopLevelDefinition)
  -> MultiHashMap PreName QName
localAliases contents = MultiHashMap.fromList
  [ (fromName $ qnameName qn, qn)
  | qn <- HashMap.keys contents
  ] <> localMethods
  where
    localMethods
      = MultiHashMap.fromList
      [ (fromName m, QName (qnameModule n) m)
      | (n, (_, Unscoped.TopLevelClassDefinition _ _ ms)) <- HashMap.toList contents
      , m <- methodName <$> ms
      ]

methodClasses
  :: HashMap QName (SourceLoc, Unscoped.TopLevelDefinition)
  -> HashMap QName QName
methodClasses contents = HashMap.fromList
  [ (QName (qnameModule n) m, n)
  | (n, (_, Unscoped.TopLevelClassDefinition _ _ ms)) <- HashMap.toList contents
  , m <- methodName <$> ms
  ]

instances
  :: [(QName, (SourceLoc, Scoped.Definition Scoped.Expr void), a)]
  -> VIX (MultiHashMap QName QName)
instances defs = fmap (MultiHashMap.fromList . concat) $ forM defs $ \(name, (_, def), _) -> case def of
  Scoped.InstanceDefinition (Scoped.InstanceDef typ _) -> do
    c <- getClass typ
    return [(c, name)]
  _ -> return mempty

importedAliases
  :: Import
  -> VIX (MultiHashMap PreName QConstr, MultiHashMap PreName QName)
importedAliases (Import modName asName exposed) = do
  otherConstrs <- liftVIX $ gets vixModuleConstrs
  otherNames <- liftVIX $ gets vixModuleNames
  let
    constrs
      = MultiHashMap.fromList
      $ concat
      [ [ (k, c)
        , (fromName (qnameName $ qconstrTypeName c) <> "." <> k, c)
        ]
      | c <- HashSet.toList $ MultiHashMap.lookup modName otherConstrs
      , let k = fromConstr $ qconstrConstr c
      ]

    names
      = MultiHashMap.fromList
      $ fmap (\n -> (fromName $ qnameName n :: PreName, n))
      $ HashSet.toList
      $ MultiHashMap.lookup modName otherNames

    exposedConstrs = case exposed of
      AllExposed -> constrs
      Exposed ns -> MultiHashMap.setIntersection constrs $ HashSet.map fromName ns

    exposedNames = case exposed of
      AllExposed -> names
      Exposed ns -> MultiHashMap.setIntersection names $ HashSet.map fromName ns

  return
    ( exposedConstrs <> MultiHashMap.mapKeys (fromQName . QName asName . fromPreName) constrs
    , exposedNames <> MultiHashMap.mapKeys (fromQName . QName asName . fromPreName) names
    )

-- | Distinguish variables from constructors, resolve scopes
resolveTopLevelDefinition
  :: Unscoped.TopLevelDefinition
  -> ResolveNames (Scoped.Definition Scoped.Expr PreName)
resolveTopLevelDefinition (Unscoped.TopLevelDefinition d) =
  Scoped.ConstantDefinition . snd <$> resolveDefinition d
resolveTopLevelDefinition (Unscoped.TopLevelDataDefinition _name params cs) = do
  (params', abstr) <- resolveParams params
  cs' <- mapM (mapM (fmap abstr . resolveExpr)) cs
  return $ Scoped.DataDefinition $ DataDef params' cs'
resolveTopLevelDefinition (Unscoped.TopLevelClassDefinition _name params ms) = do
  (params', abstr) <- resolveParams params
  ms' <- mapM (mapM (fmap abstr . resolveExpr)) ms
  return $ Scoped.ClassDefinition $ ClassDef params' ms'
resolveTopLevelDefinition (Unscoped.TopLevelInstanceDefinition typ ms) = do
  typ' <- resolveExpr typ
  ms' <- mapM (\(loc, m) -> (,) loc <$> resolveDefinition m) ms
  return
    $ Scoped.InstanceDefinition
    $ Scoped.InstanceDef typ'
    $ (\(loc, (n, d)) -> Method n loc d)
    <$> ms'

resolveParams
  :: Monad f
  => [(Plicitness, Name, Unscoped.Type)]
  -> ResolveNames (Telescope Plicitness Scoped.Expr PreName, f PreName -> Scope TeleVar f PreName)
resolveParams params = do
  params' <- forM params $ \(p, n, t) -> do
    t' <- resolveExpr t
    return (fromName n, p, t')
  let paramNames = fst3 <$> params'
      abstr = abstract $ teleAbstraction $ Vector.fromList paramNames
  return (telescope fromPreName params', abstr)

resolveDefinition
  :: Unscoped.Definition Unscoped.Expr
  -> ResolveNames (Name, Scoped.ConstantDef Scoped.Expr PreName)
resolveDefinition (Unscoped.Definition name a clauses mtyp) = do
  res <- Scoped.ConstantDef a <$> mapM resolveClause clauses <*> mapM resolveExpr mtyp
  return (name, res)

resolveClause
  :: Unscoped.Clause Unscoped.Expr
  -> ResolveNames (Scoped.Clause Scoped.Expr PreName)
resolveClause (Unscoped.Clause plicitPats e) = do
  plicitPats' <- traverse (traverse resolvePat) plicitPats
  Scoped.clause plicitPats' <$> resolveExpr e

resolveExpr
  :: Unscoped.Expr
  -> ResolveNames (Scoped.Expr PreName)
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
    Scoped.pi_ p pat' <$> resolveExpr e
  Unscoped.Lam p pat e -> do
    pat' <- resolvePat pat
    Scoped.lam p pat' <$> resolveExpr e
  Unscoped.App e1 p e2 -> Scoped.App
    <$> resolveExpr e1
    <*> pure p
    <*> resolveExpr e2
  Unscoped.Let defs body -> do
    defs' <- traverse (bitraverse pure resolveDefinition) defs
    body' <- resolveExpr body
    let sortedDefs = topoSortWith
          (\(_, (name, _)) -> fromName name)
          (\(_, (_, d)) -> toHashSet d)
          defs'

        go ds e = do
          let ds' = Vector.fromList ds
              abstr = letAbstraction $ fromName . fst . snd <$> ds'
          Scoped.Let
            ((\(loc, (name, def)) -> (loc, fromName name, Scoped.abstractConstantDef abstr def)) <$> ds')
            (abstract abstr e)

    return $ foldr go body' $ flattenSCC <$> sortedDefs
  Unscoped.Case e pats -> Scoped.case_
    <$> resolveExpr e
    <*> mapM (bitraverse resolvePat resolveExpr) pats
  Unscoped.ExternCode c -> Scoped.ExternCode <$> mapM resolveExpr c
  Unscoped.Wildcard -> return Scoped.Wildcard
  Unscoped.SourceLoc loc e -> Scoped.SourceLoc loc <$> resolveExpr e
  Unscoped.Error e -> do
    report e
    resolveExpr
      $ Unscoped.App
        (Unscoped.Var $ fromQName Builtin.StaticErrorName)
        Explicit
        (Literal.string "error\n")
        -- TODO use the actual error when strings are faster:
        -- (Literal.string $ shower $ pretty e)

resolvePat
  :: Pat PreName Unscoped.Expr PreName
  -> ResolveNames (Pat (HashSet QConstr) (Scoped.Expr PreName) PreName)
resolvePat pat = case pat of
  VarPat h v -> do
    constrCandidates <- asks (($ v) . scopeConstrs)
    if HashSet.null constrCandidates then
      return $ VarPat h v
    else do
      modify $ mappend $ HashSet.map qconstrTypeName constrCandidates
      return $ ConPat constrCandidates mempty
  WildcardPat-> return WildcardPat
  LitPat l -> return $ LitPat l
  ConPat con ps -> do
    cons <- asks (($ con) . scopeConstrs)
    forM_ cons $ \(QConstr def _) -> modify $ HashSet.insert def
    ConPat cons <$> mapM (\(p, pat') -> (,) p <$> resolvePat pat') ps
  AnnoPat p t -> AnnoPat <$> resolvePat p <*> resolveExpr t
  ViewPat t p -> ViewPat <$> resolveExpr t <*> resolvePat p
  PatLoc loc p -> PatLoc loc <$> resolvePat p

getClass
  :: Scoped.Expr v
  -> VIX QName
getClass (Scoped.Pi _ _ s) = getClass $ fromScope s
getClass (Scoped.SourceLoc loc e) = located loc $ getClass e
getClass (Scoped.appsView -> (Scoped.Global g, _)) = return g
getClass _ = throwInvalidInstance

throwInvalidInstance :: VIX a
throwInvalidInstance
  = throwLocated
  $ PP.vcat
  [ "Invalid instance"
  , "Instance types must return a class"
  , bold "Expected:" PP.<+> "an instance of the form" PP.<+> dullGreen "instance ... => C as where ..." <> ", where" PP.<+> dullGreen "C" PP.<+> "is a class."
  ]
