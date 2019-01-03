{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
module Driver.Rules where

import Protolude hiding (TypeError, moduleName, (<.>), handle)

import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.HashSet(HashSet)
import Data.List(findIndex)
import qualified Data.Text.IO as Text
import qualified Data.Text.Prettyprint.Doc as PP
import Rock
import System.Directory
import System.FilePath
import System.IO.Temp

import Analysis.Cycle
import Analysis.Denat
import qualified Analysis.ReturnDirection as ReturnDirection
import Analysis.Simplify
import Backend.ClosureConvert
import qualified Backend.Compile
import qualified Backend.ExtractExtern as ExtractExtern
import qualified Backend.Generate as Generate
import qualified Backend.Generate.Submodule as Generate
import Backend.Lift
import qualified Backend.SLam as SLam
import Backend.Target
import qualified Builtin
import qualified Builtin.Names as Builtin
import qualified Command.Compile.Options as Compile
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
import Util.TopoSort
import VIX

rules
  :: LogEnv
  -> [FilePath]
  -> (FilePath -> IO Text)
  -> Target
  -> GenRules (Writer [Error] Query) Query
rules logEnv_ inputFiles readFile_ target (Writer query) = case query of
  Files -> Input $ noError $ do
    builtinFile <- liftIO $ getDataFileName "rts/Builtin.vix"
    return $ inputFiles <> pure builtinFile

  File file -> Input $ noError $ readFile_ file

  Driver.Query.Target -> Input $ noError $ return target

  Builtins -> Task $ noError $ do
    target_ <- fetch Driver.Query.Target
    return $ Builtin.environment target_

  ParsedModule file -> Task $ do
    text <- fetch $ File file
    case Parse.parseText Parse.modul text file of
      Left err -> do
        let mh = ModuleHeader "Main" noneExposed mempty
        return ((mh, mempty), pure err)
      Right a -> return (a, mempty)

  ModuleHeaders -> Task $ do
    fileNames <- fetch Files
    result <- for fileNames $ \file ->
      (,) file <$> fetchModuleHeader file
    withReportEnv $ \reportEnv_ ->
      flip runReaderT reportEnv_
      $ HashMap.fromList <$> cycleCheckModules result

  ModuleFiles -> Task $ noError $ do
    moduleHeaders <- fetch ModuleHeaders
    return
      $ HashMap.fromList
      [(moduleName mh, fp) | (fp, mh) <- HashMap.toList moduleHeaders]

  ModuleFile moduleName_ -> Task $ noError $
    HashMap.lookup moduleName_ <$> fetch ModuleFiles

  DupCheckedModule moduleName_ -> Task $ do
    maybeFile <- fetch $ ModuleFile moduleName_
    case maybeFile of
      Nothing -> return mempty
      Just file -> do
        (moduleHeader_, defs) <- fetch $ ParsedModule file
        return $ DupCheck.dupCheck (moduleName moduleHeader_) defs

  ModuleExports moduleName_ -> Task $ noError $ do
    maybeFile <- fetch $ ModuleFile moduleName_
    case maybeFile of
      Nothing -> return mempty
      Just file -> do
        (moduleHeader_, _) <- fetch $ ParsedModule file
        defs <- fetch $ DupCheckedModule moduleName_
        return $ ResolveNames.moduleExports moduleHeader_ defs

  ResolvedModule moduleName_ -> Task $ do
    defs <- fetch $ DupCheckedModule moduleName_
    maybeFile <- fetch $ ModuleFile moduleName_
    case maybeFile of
      Nothing -> return mempty
      Just file -> do
        (moduleHeader_, _) <- fetch $ ParsedModule file
        withReportEnv $ \reportEnv_ ->
          runVIX logEnv_ reportEnv_ $
            ResolveNames.resolveModule moduleHeader_ defs

  ResolvedBindingGroups moduleName_ -> Task $ noError $ do
    resolvedModule <- fetch $ ResolvedModule moduleName_
    return
      $ HashMap.fromList
        [ (bindingGroupNames bindingGroup, bindingGroup)
        | bindingGroup <- resolvedModule
        ]

  BindingGroupMap moduleName_ -> Task $ noError $ do
    bindingGroupsMap <- fetch $ ResolvedBindingGroups moduleName_
    return
      $ HashMap.fromList
      [ (name, bindingGroup)
      | bindingGroup <- HashMap.keys bindingGroupsMap
      , name <- HashSet.toList bindingGroup
      ]

  BindingGroup name -> Task $ noError $ do
    let module_ = qnameModule name
    case module_ of
      Builtin.RuntimeModuleName -> do
        target_ <- fetch Driver.Query.Target
        return $ HashSet.fromMap $ void $ Builtin.convertedEnvironment target_
      _ ->
        -- TODO: Empty binding groups can currently happen for builtins. Is there a
        -- cleaner solution?
        HashMap.lookupDefault mempty name <$> fetch (BindingGroupMap module_)

  ElaboratedGroup names -> Task $ logCoreTerms logEnv_ "elaborated" $ do
    -- TODO check for Sixten.Builtin prefix first?
    builtins <- fetch Builtins
    case traverse (\qn -> (,) (gname qn) <$> HashMap.lookup qn builtins) $ toList names of
      Just results -> return (HashMap.fromList results, [])
      Nothing -> case toList names of
        [] -> return mempty
        name:_ -> do
          let moduleName_ = qnameModule name
          bindingGroups <- fetch $ ResolvedBindingGroups moduleName_
          let
            bindingGroup
              = fromMaybe (panic "No such binding group")
              $ HashMap.lookup names bindingGroups
          (result, errs) <- withReportEnv $ \reportEnv_ ->
            runVIX logEnv_ reportEnv_ $ do
              result <- TypeCheck.runElaborate moduleName_
                $ TypeCheck.checkAndGeneraliseTopLevelDefs
                $ toVector bindingGroup
              cycleCheck result
          let resultMap = toHashMap $ (\(n, l, d, t) -> (n, (l, d, t))) <$> result
          return (resultMap, errs)

  SimplifiedGroup names -> Task $ logCoreTerms logEnv_ "simplified" $ noError $ do
    defs <- fetch $ ElaboratedGroup names
    return $ flip HashMap.map defs $ \(loc, ClosedDefinition def, Biclosed typ) ->
      ( loc
      , ClosedDefinition $ simplifyDef globTerm def
      , Biclosed $ simplifyExpr globTerm 0 typ
      )
    where
      globTerm x = not $ HashSet.member (gnameBaseName x) names

  Type name -> Task $ noError $ do
    bindingGroup <- fetch $ BindingGroup $ gnameBaseName name
    defs <- fetch $ SimplifiedGroup bindingGroup
    let
      (_loc, _def, typ)
         = HashMap.lookupDefault (panic $ "fetch Type " <> show name) name defs
    return typ

  Definition name -> Task $ noError $ do
    bindingGroup <- fetch $ BindingGroup $ gnameBaseName name
    defs <- fetch $ SimplifiedGroup bindingGroup
    let
      (_loc, def, _typ)
        = HashMap.lookupDefault (panic $ "fetch Definition " <> show name) name defs
    return def

  QConstructor (QConstr typeName c) -> Task $ noError $ do
    def <- fetchDefinition $ gname typeName
    case def of
      DataDefinition ddef _ -> do
        let qcs = Core.quantifiedConstrTypes ddef implicitise
        case filter ((== c) . constrName) qcs of
          [] -> panic "fetch QConstructor []"
          cdef:_ -> return $ biclose identity identity $ constrType cdef
      ConstantDefinition {} -> panic "fetch QConstructor ConstantDefinition"

  ClassMethods className -> Task $ noError $ do
    dupChecked <- fetch $ DupCheckedModule $ qnameModule className
    let (_loc, def) = HashMap.lookupDefault (panic "fetch ClassMethods") className dupChecked
    case def of
      Unscoped.TopLevelClassDefinition _ _ methods ->
        return $ Just $ (\(Method name loc _) -> (name, loc)) <$> methods
      _ -> return Nothing

  Instances moduleName_ -> Task $ noError $ do
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

  ConstrIndex (QConstr typeName c) -> Task $ noError $ do
    def <- fetchDefinition $ gname typeName
    case def of
      DataDefinition (DataDef _ constrDefs) _ ->
        case constrDefs of
          [] -> return Nothing
          [_] -> return Nothing
          _ -> case findIndex ((== c) . constrName) constrDefs of
            Nothing -> panic "fetch ConstrIndex []"
            Just i -> return $ Just $ fromIntegral i
      ConstantDefinition {} -> panic "fetch ConstrIndex ConstantDefinition"

  LambdaLifted bindingGroup -> Task $ do
    coreDefs <- fetch $ SimplifiedGroup bindingGroup
    withReportEnv $ \reportEnv_ ->
      fmap concat $ for (HashMap.toList coreDefs) $ \(name, (_, ClosedDefinition def, _)) ->
        runVIX logEnv_ reportEnv_ $ do
          def' <- SLam.runSlam $ SLam.slamDef def
          let def'' = denatAnno def'
          liftToDefinition name $ close (panic "LambdaLifted close") def''

  ConvertedSignatures bindingGroup -> Task $ do
    liftedDefs <- fetch $ LambdaLifted bindingGroup
    withReportEnv $ \reportEnv_ ->
      fmap HashMap.fromList $ for liftedDefs $ \(name, def) ->
        runVIX logEnv_ reportEnv_ $ do
          res <- runConvertedSignature name def
          return (name, res)

  ConvertedSignature name -> Task $ noError $ do
    bindingGroup <- fetch $ BindingGroup $ gnameBaseName name
    signatures <- fetch $ ConvertedSignatures bindingGroup
    return $ fst $ HashMap.lookupDefault (Nothing, mempty) name signatures

  RuntimeDefinitions -> Task $ noError $ do
    target_ <- fetch Driver.Query.Target
    return $ Builtin.convertedEnvironment target_

  Converted bindingGroup -> Task $
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

  DirectionSignatures bindingGroup -> Task $ do
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

  DirectionSignature name -> Task $ noError $ do
    bindingGroup <- fetch $ BindingGroup $ gnameBaseName name
    sigs <- fetch $ DirectionSignatures bindingGroup
    case HashMap.lookup name sigs of
      Just (_, sig) -> return $ Just sig
      Nothing -> do
        extracted <- fetch $ ExtractedSubmodules bindingGroup
        return
          $ listToMaybe
          $ mapMaybe
            (HashMap.lookup name . Extracted.submoduleSignatures . snd)
            extracted

  ExtractedSubmodules bindingGroup -> Task $ do
    defs <- fetch $ DirectionSignatures bindingGroup
    withReportEnv $ \reportEnv_ ->
      runVIX logEnv_ reportEnv_ $
        fmap concat $ for (HashMap.toList defs) $ \(name, (def, _sig)) ->
          ExtractExtern.extractDef name def

  GeneratedSubmodules bindingGroup -> Task $ do
    extracted <- fetch $ ExtractedSubmodules bindingGroup
    withReportEnv $ \reportEnv_ ->
      runVIX logEnv_ reportEnv_ $
        for extracted $ uncurry Generate.generateSubmodule

  CheckAll -> Task $ noError $ do
    modules <- fetchModules
    fmap concat $ for (toList modules) $ \module_ -> do
      bindingGroups <- fetchBindingGroups module_
      for (toList bindingGroups) $ \names ->
        fetch $ ElaboratedGroup names

  CompileAll outputFile opts -> Task $ noError $ do
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

    inputFiles_ <- fetch Files
    target_ <- fetch Driver.Query.Target
    liftIO $ compileModules inputFiles_ outputFile target_ opts (runtimeSubmodule : submodules)

noError :: (Monoid w, Functor f) => f a -> f (a, w)
noError = fmap (, mempty)

withReportEnv :: MonadIO m => (ReportEnv -> m a) -> m (a, [Error])
withReportEnv f = do
  errVar <- liftIO $ newMVar []
  a <- f ReportEnv
    { _currentLocation = Nothing
    , _reportAction = \err ->
      modifyMVar_ errVar $ \errs -> pure $ err:errs
    }
  errs <- liftIO $ readMVar errVar
  return (a, errs)

-- TODO Move
cycleCheckModules
  :: (Foldable t, MonadReport m)
  => t (x, ModuleHeader)
  -> m [(x, ModuleHeader)]
cycleCheckModules modules = do
  let orderedModules = moduleDependencyOrder modules
  fmap concat $ forM orderedModules $ \case
    AcyclicSCC modul -> return [modul]
    CyclicSCC ms -> do
      -- TODO: Could be allowed?
      -- TODO: Maybe this should be a different kind of error?
      report
        $ TypeError
          ("Circular modules:"
          PP.<+> PP.hsep (PP.punctuate PP.comma $ fromModuleName . moduleName . snd <$> ms))
          Nothing
          mempty
      let
        cyclicModuleNames = HashSet.fromList $ moduleName . snd <$> ms
        removeCyclicImports (x, m) =
          ( x
          , m
            { moduleImports = filter
              (not . (`HashSet.member` cyclicModuleNames) . importModule)
              $ moduleImports m
            }
          )
      return $ removeCyclicImports <$> ms

-- TODO refactor
compileModules
  :: [FilePath]
  -> FilePath
  -> Target
  -> Compile.Options
  -> [(ModuleHeader, [Generate.Submodule])]
  -> IO ()
compileModules inputFiles outputFile target_ opts modules =
  withAssemblyDir (Compile.assemblyDir opts) $ \asmDir -> do
    (externFiles, llFiles)
      <- fmap mconcat $ forM modules $ \(moduleHeader, subModules) -> do
        let fileBase = asmDir </> fromModuleName (moduleName moduleHeader)
            llName = fileBase <> ".ll"
            cName = fileBase <> ".c"
        externs <- writeModule moduleHeader subModules llName [(C, cName)]
        return (externs, [llName])
    let linkedLlFileName = asmDir </> firstFileName <.> "linked" <.> "ll"
    Backend.Compile.compile opts Backend.Compile.Arguments
      { Backend.Compile.cFiles = [cFile | (C, cFile) <- externFiles]
      , Backend.Compile.llFiles = llFiles
      , Backend.Compile.linkedLlFileName = linkedLlFileName
      , Backend.Compile.target = target_
      , Backend.Compile.outputFile = outputFile
      }
  where
   -- TODO should use the main file instead
    firstFileName = takeBaseName $ fromMaybe "output" $ head inputFiles

    withAssemblyDir Nothing k = withSystemTempDirectory "sixten" k
    withAssemblyDir (Just dir) k = do
      createDirectoryIfMissing True dir
      k dir

-- TODO move
writeModule
  :: ModuleHeader
  -> [Generate.Submodule]
  -> FilePath
  -> [(Language, FilePath)]
  -> IO [(Language, FilePath)]
writeModule moduleHeader subModules llOutputFile externOutputFiles = do
  Util.withFile llOutputFile WriteMode $
    Generate.writeLlvmModule
      (moduleName moduleHeader)
      (moduleImports moduleHeader)
      subModules
  fmap catMaybes $
    forM externOutputFiles $ \(lang, outFile) ->
      case fmap snd $ filter ((== lang) . fst) $ concatMap Generate.externs subModules of
        [] -> return Nothing
        externCode -> Util.withFile outFile WriteMode $ \handle -> do
          -- TODO this is C specific
          Text.hPutStrLn handle "#include <inttypes.h>"
          Text.hPutStrLn handle "#include <stdint.h>"
          Text.hPutStrLn handle "#include <stdio.h>"
          Text.hPutStrLn handle "#include <stdlib.h>"
          Text.hPutStrLn handle "#include <string.h>"
          Text.hPutStrLn handle "#ifdef _WIN32"
          Text.hPutStrLn handle "#include <io.h>"
          Text.hPutStrLn handle "#else"
          Text.hPutStrLn handle "#include <unistd.h>"
          Text.hPutStrLn handle "#endif"
          forM_ externCode $ \code -> do
            Text.hPutStrLn handle ""
            Text.hPutStrLn handle code
          return $ Just (lang, outFile)

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

bindingGroupNames :: [(QName, loc, Closed (Pre.Definition s))] -> HashSet QName
bindingGroupNames = toHashSet . concatMap go
  where
    go (name, _, Closed (Pre.ClassDefinition cd))
      = pure name <> (QName (qnameModule name) . methodName <$> classMethods cd)
    go (name, _, _)
      = pure name
