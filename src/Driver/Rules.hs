{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
module Driver.Rules where

import Protolude hiding (TypeError, moduleName, (<.>), handle)

import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.HashSet(HashSet)
import Data.List(findIndex)
import Rock

import Analysis.Cycle
import Analysis.Denat
import qualified Analysis.ReturnDirection as ReturnDirection
import Analysis.Simplify
import Analysis.Termination
import Backend.ClosureConvert
import qualified Backend.Compile
import qualified Backend.ExtractExtern as ExtractExtern
import qualified Backend.Generate as Generate
import Backend.Lift
import qualified Backend.SLam as SLam
import Backend.Target
import qualified Builtin
import qualified Builtin.Names as Builtin
import Driver.Query
import Effect
import qualified Elaboration.Monad as TypeCheck
import qualified Elaboration.TypeCheck.Definition as TypeCheck
import Error
import Frontend.DupCheck as DupCheck
import qualified Frontend.Parse as Parse
import qualified Frontend.ResolveNames as ResolveNames
import Paths_sixten
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Pre.Definition as Pre
import qualified Syntax.Pre.Unscoped as Unscoped
import qualified Syntax.Sized.Extracted as Extracted
import Util
import VIX

rules
  :: LogEnv
  -> [FilePath]
  -> (FilePath -> IO Text)
  -> Target
  -> GenRules (Writer [Error] (Writer TaskKind Query)) Query
rules logEnv_ inputFiles readFile_ target (Writer (Writer query)) = case query of
  Files -> input $ do
    builtinFile <- liftIO $ getDataFileName "rts/Builtin.vix"
    return (inputFiles <> pure builtinFile)

  File file -> input $ liftIO $ readFile_ file

  Driver.Query.Target -> input $ return target

  Builtins -> noError $ do
    target_ <- fetch Driver.Query.Target
    return $ Builtin.environment target_

  ParsedModule file -> nonInput $ do
    text <- fetch $ File file
    case Parse.parseText Parse.modul text file of
      (Left err, highlights) -> do
        let mh = ModuleHeader "Main" noneExposed mempty
        return ((mh, mempty, highlights), pure err)
      (Right (moduleHeader, errDefs), highlights) -> do
        let
          (errs, defs) = partitionEithers errDefs
        return ((moduleHeader, defs, highlights), errs)

  Driver.Query.AbsoluteSourceLoc name -> noError $ do
    mfile <- fetch $ ModuleFile $ qnameModule name
    case mfile of
      Nothing -> panic "fetch AbsoluteSourceLoc no file"
      Just file -> do
        (_, defs, _) <- fetch $ ParsedModule file
        return $ case find ((==) name . fst3) defs of
          Nothing -> panic "fetch AbsoluteSourceLoc no def"
          Just (_, loc, _) -> loc

  ModuleHeaders -> nonInput $ do
    fileNames <- fetch Files
    result <- for fileNames $ \file ->
      (,) file <$> fetchModuleHeader file
    withReportEnv $ \reportEnv_ ->
      flip runReaderT reportEnv_
      $ HashMap.fromList <$> cycleCheckModules result

  ModuleFiles -> noError $ do
    moduleHeaders <- fetch ModuleHeaders
    return
      $ HashMap.fromList
      [(moduleName mh, fp) | (fp, mh) <- HashMap.toList moduleHeaders]

  ModuleFile moduleName_ -> noError $
    HashMap.lookup moduleName_ <$> fetch ModuleFiles

  DupCheckedModule moduleName_ -> nonInput $ do
    maybeFile <- fetch $ ModuleFile moduleName_
    case maybeFile of
      Nothing -> return mempty
      Just file -> do
        (_, defs, _) <- fetch $ ParsedModule file
        DupCheck.dupCheck defs

  ModuleExports moduleName_ -> noError $ do
    maybeFile <- fetch $ ModuleFile moduleName_
    case maybeFile of
      Nothing -> return mempty
      Just file -> do
        (moduleHeader_, _, _) <- fetch $ ParsedModule file
        defs <- fetch $ DupCheckedModule moduleName_
        return $ ResolveNames.moduleExports moduleHeader_ defs

  ResolvedModule moduleName_ -> nonInput $ do
    defs <- fetch $ DupCheckedModule moduleName_
    maybeFile <- fetch $ ModuleFile moduleName_
    case maybeFile of
      Nothing -> return mempty
      Just file -> do
        (moduleHeader_, _, _) <- fetch $ ParsedModule file
        withReportEnv $ \reportEnv_ ->
          runVIX logEnv_ reportEnv_ $
            ResolveNames.resolveModule moduleHeader_ defs

  ResolvedBindingGroups moduleName_ -> noError $ do
    resolvedModule <- fetch $ ResolvedModule moduleName_
    return
      $ HashMap.fromList
        [ (bindingGroupNames bindingGroup, bindingGroup)
        | bindingGroup <- resolvedModule
        ]

  ResolvedBindingGroup moduleName_ names -> noError $ do
    bindingGroups <- fetch $ ResolvedBindingGroups moduleName_
    return
      $ fromMaybe (panic "No such binding group")
      $ HashMap.lookup names bindingGroups

  BindingGroupMap moduleName_ -> noError $ do
    bindingGroupsMap <- fetch $ ResolvedBindingGroups moduleName_
    return
      $ HashMap.fromList
      [ (name, bindingGroup)
      | bindingGroup <- HashMap.keys bindingGroupsMap
      , name <- HashSet.toList bindingGroup
      ]

  BindingGroup name -> noError $ do
    let module_ = qnameModule name
    case module_ of
      Builtin.RuntimeModuleName -> do
        target_ <- fetch Driver.Query.Target
        return $ HashSet.fromMap $ void $ Builtin.convertedEnvironment target_
      _ ->
        -- TODO: Empty binding groups can currently happen for builtins. Is there a
        -- cleaner solution?
        HashMap.lookupDefault mempty name <$> fetch (BindingGroupMap module_)

  ElaboratedGroup names -> nonInput $ logCoreTerms logEnv_ "elaborated" $ do
    -- TODO check for Sixten.Builtin prefix first?
    builtins <- fetch Builtins
    case traverse (\qn -> (,) (gname qn) <$> HashMap.lookup qn builtins) $ toList names of
      Just results -> return (HashMap.fromList results, [])
      Nothing ->
        case toList names of
          [] -> return mempty
          name:_  -> do
            let
              moduleName_ = qnameModule name
            bindingGroup <- fetch $ ResolvedBindingGroup moduleName_ names
            (result, errs) <- withReportEnv $ \reportEnv_ ->
              runVIX logEnv_ reportEnv_ $ do
                result <- TypeCheck.runElaborate moduleName_
                  $ TypeCheck.checkAndGeneraliseTopLevelDefs
                  $ toVector bindingGroup
                cycleCheck result
            let resultMap = toHashMap $ (\(n, l, d, t) -> (n, (l, d, t))) <$> result
            return (resultMap, errs)

  SimplifiedGroup names -> nonInput $ logCoreTerms logEnv_ "simplified" $ do
    defs <- fetch $ ElaboratedGroup names
    withReportEnv $ \reportEnv_ ->
      runVIX logEnv_ reportEnv_ $ withContextEnvT $
        forM defs $ \(loc, ClosedDefinition def, Biclosed typ) -> do
          def' <- simplifyDef globTerm def
          typ' <- simplifyExpr globTerm typ
          return
            ( loc
            , closeDefinition identity (panic "fetch SimplifiedGroup") def'
            , biclose identity (panic "fetch SimplifiedGroup") typ'
            )
    where
      globTerm x = not $ HashSet.member (gnameBaseName x) names

  Type name -> noError $ do
    bindingGroup <- fetch $ BindingGroup $ gnameBaseName name
    defs <- fetch $ SimplifiedGroup bindingGroup
    let
      (_loc, _def, typ)
         = HashMap.lookupDefault (panic $ "fetch Type " <> show name) name defs
    return typ

  Definition name -> noError $ do
    bindingGroup <- fetch $ BindingGroup $ gnameBaseName name
    defs <- fetch $ SimplifiedGroup bindingGroup
    let
      (_loc, def, _typ)
        = HashMap.lookupDefault (panic $ "fetch Definition " <> show name) name defs
    return def

  QConstructor (QConstr typeName c) -> noError $ do
    def <- fetchDefinition $ gname typeName
    case def of
      DataDefinition ddef@(DataDef _ params _) _ -> do
        let qcs = Core.quantifiedConstrTypes ddef implicitise
        case filter ((== c) . constrName) qcs of
          [] -> panic "fetch QConstructor []"
          cdef:_ -> return (teleLength params, biclose identity identity $ constrType cdef)
      ConstantDefinition {} -> panic "fetch QConstructor ConstantDefinition"

  ClassMethods className -> noError $ do
    dupChecked <- fetch $ DupCheckedModule $ qnameModule className
    let (_loc, def) = HashMap.lookupDefault (panic "fetch ClassMethods") className dupChecked
    case def of
      Unscoped.ClassDefinition _ methods ->
        return $ Just $ (\(Method name loc _) -> (name, loc)) <$> methods
      _ -> return Nothing

  Instances moduleName_ -> noError $ do
    maybeFile <- fetch $ ModuleFile moduleName_
    case maybeFile of
      Nothing -> return mempty
      Just file -> do
        moduleHeader_ <- fetchModuleHeader file
        dependencyInstances <- for (moduleImports moduleHeader_) $ \import_ ->
          fetch $ Instances $ importModule import_
        resolvedModule <- fetch $ ResolvedModule moduleName_
        let flatModule = concat resolvedModule
        -- These errors are reported by ResolveNames, so we ignore them here.
        (res, _errs) <- withReportEnv $ \reportEnv_ ->
          runVIX logEnv_ reportEnv_ $
            ResolveNames.instances
              $ (\(n, loc, Closed def) -> (n, loc, def)) <$> flatModule
        return $ res <> mconcat dependencyInstances

  InlinedDefinition name -> noError $ do
    def <- fetchDefinition name
    return $ case def of
      ConstantDefinition Concrete e
        | duplicable e -> Just $ biclose identity identity e
      ConstantDefinition {} -> Nothing
      DataDefinition _ _ -> Nothing

  ConstrIndex (QConstr typeName c) -> noError $ do
    def <- fetchDefinition $ gname typeName
    case def of
      DataDefinition (DataDef _ _ constrDefs) _ ->
        case constrDefs of
          [] -> return Nothing
          [_] -> return Nothing
          _ -> case findIndex ((== c) . constrName) constrDefs of
            Nothing -> panic "fetch ConstrIndex []"
            Just i -> return $ Just $ fromIntegral i
      ConstantDefinition {} -> panic "fetch ConstrIndex ConstantDefinition"

  LambdaLifted bindingGroup -> nonInput $ logTerms logEnv_ "lifted" fst snd $ do
    coreDefs <- fetch $ SimplifiedGroup bindingGroup
    withReportEnv $ \reportEnv_ ->
      fmap concat $ for (HashMap.toList coreDefs) $ \(name, (_, ClosedDefinition def, _)) ->
        runVIX logEnv_ reportEnv_ $ do
          def' <- SLam.runSLam $ SLam.slamDef def
          let def'' = denatAnno def'
          liftToDefinition name $ close (panic "LambdaLifted close") def''

  ConvertedSignatures bindingGroup -> nonInput $ do
    liftedDefs <- fetch $ LambdaLifted bindingGroup
    withReportEnv $ \reportEnv_ ->
      fmap HashMap.fromList $ for liftedDefs $ \(name, def) ->
        runVIX logEnv_ reportEnv_ $ do
          res <- runConvertedSignature name def
          return (name, res)

  ConvertedSignature name -> noError $ do
    bindingGroup <- fetch $ BindingGroup $ gnameBaseName name
    signatures <- fetch $ ConvertedSignatures bindingGroup
    return $ fst $ HashMap.lookupDefault (Nothing, mempty) name signatures

  RuntimeDefinitions -> noError $ do
    target_ <- fetch Driver.Query.Target
    return $ Builtin.convertedEnvironment target_

  Converted bindingGroup -> nonInput $ logTerms logEnv_ "converted" fst snd $
    case qnameModule <$> toList bindingGroup of
      Builtin.RuntimeModuleName:_ -> do
        runtimeDefs <- fetch RuntimeDefinitions
        let
          result = foreach (toList bindingGroup) $ \name ->
            ( gname name
            , fromMaybe (panic "Converted Runtime def")
              $ HashMap.lookup name runtimeDefs
            )
        return (result, mempty)
      _ ->
        withReportEnv $ \reportEnv_ -> do
          liftedDefs <- fetch $ LambdaLifted bindingGroup
          signatures <- fetch $ ConvertedSignatures bindingGroup
          fmap concat $ for liftedDefs $ \(name, def) ->
            runVIX logEnv_ reportEnv_ $ do
              let
                (_, convertedSigDefs) = HashMap.lookupDefault (Nothing, mempty) name signatures
              convertedDefs <- runConvertDefinition name def
              return $ convertedSigDefs <> convertedDefs

  DirectionSignatures bindingGroup -> nonInput $ do
    convertedDefs <- fetch $ Converted bindingGroup
    withReportEnv $ \reportEnv_ ->
      runVIX logEnv_ reportEnv_ $ do
        results <- ReturnDirection.inferRecursiveDefs $ toVector convertedDefs
        -- TODO do we need this dependency order?

        -- results <- for (Sized.dependencyOrder convertedDefs) $ \defGroup -> do
        --   result <- fmap toList $ ReturnDirection.inferRecursiveDefs $ toVector defGroup
        --   return result
        return
          $ toHashMap
          $ (\(name, def, sig) -> (name, (def, sig))) <$> results

  DirectionSignature name -> noError $ do
    bindingGroup <- fetch $ BindingGroup $ gnameBaseName name
    sigs <- fetch $ DirectionSignatures bindingGroup
    case HashMap.lookup name sigs of
      Just (_, sig) -> return $ Just sig
      Nothing -> do
        extracted <- fetch $ Extracted bindingGroup
        return
          $ listToMaybe
          $ mapMaybe
            (HashMap.lookup name . Extracted.extractedSignatures . snd3)
            extracted

  Extracted bindingGroup -> nonInput $ logTerms logEnv_ "extracted" fst3 thd3 $ do
    defs <- fetch $ DirectionSignatures bindingGroup
    withReportEnv $ \reportEnv_ ->
      runVIX logEnv_ reportEnv_ $
        fmap concat $ for (HashMap.toList defs) $ \(name, (def, _sig)) ->
          ExtractExtern.extractDef name def

  GeneratedSubmodules bindingGroup -> nonInput $ do
    extracted <- fetch $ Extracted bindingGroup
    withReportEnv $ \reportEnv_ ->
      runVIX logEnv_ reportEnv_ $
        for extracted $ uncurry3 Generate.generateSubmodule

  CheckAll -> noError $ do
    modules <- fetchModules
    fmap concat $ for (toList modules) $ \module_ -> do
      bindingGroups <- fetchBindingGroups module_
      for (toList bindingGroups) $ \names ->
        fetch $ ElaboratedGroup names

  CompileAll outputFile opts -> noError $ do
    moduleHeaders <- fetch ModuleHeaders
    submodules <- for (HashMap.elems moduleHeaders) $ \moduleHeader -> do
      bindingGroups <- fetch $ ResolvedModule $ moduleName moduleHeader
      submodules <- for bindingGroups $ \defs ->
        fetch $ GeneratedSubmodules $ bindingGroupNames defs
      return (moduleHeader, concat submodules)

    runtimeSubmodule <- do
      runtimeBindingGroup <- fetch $ BindingGroup $ Builtin.applyName 1
      runtimeSubmodule <- fetch $ GeneratedSubmodules runtimeBindingGroup
      return (ModuleHeader Builtin.RuntimeModuleName AllExposed mempty, runtimeSubmodule)

    target_ <- fetch Driver.Query.Target
    liftIO $ Backend.Compile.compileModules outputFile target_ opts (runtimeSubmodule : submodules)

noError :: (Monoid w, Functor f) => f a -> f ((a, TaskKind), w)
noError = fmap ((, mempty) . (, NonInput))

nonInput :: Functor f => f (a, w) -> f ((a, TaskKind), w)
nonInput = fmap $ first (, NonInput)

input :: (Monoid w, Functor f) => f a -> f ((a, TaskKind), w)
input = fmap ((, mempty) . (, Input))

withReportEnv :: MonadIO m => (ReportEnv -> m a) -> m (a, [Error])
withReportEnv f = do
  errVar <- liftIO $ newMVar []
  a <- f $ emptyReportEnv $ \err ->
    modifyMVar_ errVar $ \errs -> pure $ err:errs
  errs <- liftIO $ readMVar errVar
  return (a, errs)

logCoreTerms
  :: MonadIO m
  => LogEnv
  -> Category
  -> m (ElaboratedGroup, errs)
  -> m (ElaboratedGroup, errs)
logCoreTerms logEnv_ c@(Category ct) m = do
  result@(defs, _) <- m
  flip runReaderT logEnv_ $
    whenLoggingCategory c $ do
      Effect.log $ "----- [" <> ct <> "] -----"
      forM_ (HashMap.toList defs) $ \(n, (_, ClosedDefinition d, Biclosed t)) -> do
        Effect.log
          $ showWide
          $ pretty
          $ prettyM n <+> ":" <+> prettyM (t :: Core.Expr Void Doc)
        Effect.log
          $ showWide
          $ pretty
          $ prettyNamed (prettyM n) (d :: Definition (Core.Expr Void) Doc)
        Effect.log ""
  return result

logTerms
  :: (MonadIO m, Pretty name, Pretty term)
  => LogEnv
  -> Category
  -> (def -> name)
  -> (def -> term)
  -> m ([def], errs)
  -> m ([def], errs)
logTerms logEnv_ c@(Category ct) name term m = do
  result@(defs, _) <- m
  flip runReaderT logEnv_ $
    whenLoggingCategory c $ do
      Effect.log $ "----- [" <> ct <> "] -----"
      forM_ defs $ \def -> do
        Effect.log
          $ showWide
          $ pretty
          $ prettyM (name def) <+> "=" <+> prettyM (term def)
        Effect.log ""
  return result

bindingGroupNames :: [(QName, loc, Closed (Pre.Definition s))] -> HashSet QName
bindingGroupNames = toHashSet . concatMap go
  where
    go (name, _, Closed (Pre.ClassDefinition cd))
      = pure name <> (QName (qnameModule name) . methodName <$> classMethods cd)
    go (name, _, _)
      = pure name
