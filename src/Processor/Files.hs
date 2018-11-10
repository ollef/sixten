{-# LANGUAGE FlexibleContexts, LambdaCase, OverloadedStrings #-}
module Processor.Files where

import Protolude hiding (TypeError, moduleName, sourceFile)

import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.List.NonEmpty(NonEmpty)
import qualified Data.Text.Prettyprint.Doc as PP
import System.FilePath

import qualified Backend.Generate as Generate
import Backend.Target
import qualified Builtin
import qualified Frontend.Parse as Parse
import Paths_sixten(getDataFileName)
import qualified Processor.File as File
import Processor.Result
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Pre.Unscoped as Unscoped
import Util.TopoSort
import VIX

data Arguments = Arguments
  { sourceFiles :: NonEmpty FilePath
  , assemblyDir :: !FilePath
  , target :: !Target
  , logHandle :: !Handle
  , verbosity :: !Int
  , silentErrors :: !Bool
  } deriving (Eq, Show)

data ProcessFilesResult = ProcessFilesResult
  { externFiles :: [(Language, FilePath)]
  , llFiles :: [FilePath]
  }

instance Semigroup ProcessFilesResult where
  ProcessFilesResult c1 l1 <> ProcessFilesResult c2 l2
    = ProcessFilesResult (c1 <> c2) (l1 <> l2)

instance Monoid ProcessFilesResult where
  mempty = ProcessFilesResult mempty mempty
  mappend = (<>)

parseFiles
  :: NonEmpty FilePath
  -> IO (Result [(ModuleHeader, [(SourceLoc, Unscoped.TopLevelDefinition)])])
parseFiles srcFiles = do
  moduleResults <- forM srcFiles $ \sourceFile -> do
    parseResult <- Parse.parseFromFileEx Parse.modul sourceFile
    return $ pure <$> parseResult
  return $ sconcat moduleResults

parseVirtualFiles
  :: NonEmpty (FilePath, Text)
  -> Result [(ModuleHeader, [(SourceLoc, Unscoped.TopLevelDefinition)])]
parseVirtualFiles srcFiles = do
  let moduleResults = foreach srcFiles $ \(sourceFile, s) -> do
        let parseResult = Parse.parseText Parse.modul s sourceFile
        pure <$> parseResult
  sconcat moduleResults

checkFiles :: Arguments -> IO (Result [Error])
checkFiles args = do
  parseResult <- parseFiles $ sourceFiles args
  fmap join $ forM parseResult $ \modules -> do
    let go = do
          _ <- compileBuiltins -- Done only for the side effects
          orderedModules <- cycleCheck modules
          mapM_ (File.frontend $ const $ return []) orderedModules
    fmap snd <$> runVIX go (target args) (logHandle args) (verbosity args) (silentErrors args)

checkVirtualFiles
  :: NonEmpty (FilePath, Text)
  -> IO (Result ([[(QName, SourceLoc, ClosedDefinition Core.Expr, Biclosed Core.Expr)]], [Error]))
checkVirtualFiles files = do
  let parseResult = parseVirtualFiles files
  let args = Arguments
        { sourceFiles = fst <$> files
        , assemblyDir = ""
        , target = defaultTarget
        , logHandle = stdout
        , verbosity = 0
        , silentErrors = True
        }
  fmap join $ forM parseResult $ \modules -> do
    let go = do
          _ <- compileBuiltins -- Done only for the side effects
          orderedModules <- cycleCheck modules
          mapM (File.frontend pure) orderedModules
    runVIX go (target args) (logHandle args) (verbosity args) (silentErrors args)

processFiles :: Arguments -> IO (Result (ProcessFilesResult, [Error]))
processFiles args = do
  parseResult <- parseFiles $ sourceFiles args
  fmap join $ forM parseResult $ \modules -> do
    let go = do
          builtins <- compileBuiltins
          orderedModules <- cycleCheck modules
          compiledModules <- forM orderedModules $ \(moduleHeader, subModules) -> do
            compiledModule <- File.process (moduleHeader, subModules)
            return (moduleHeader, compiledModule)
          writeModules (assemblyDir args) $ builtins : compiledModules
    runVIX go (target args) (logHandle args) (verbosity args) (silentErrors args)

cycleCheck
  :: (Foldable t, MonadError Error m)
  => t (ModuleHeader, contents)
  -> m [(ModuleHeader, contents)]
cycleCheck modules = do
  let orderedModules = moduleDependencyOrder modules
  forM orderedModules $ \case
    AcyclicSCC modul -> return modul
    CyclicSCC ms -> throwError
      -- TODO: Could be allowed?
      -- TODO: Maybe this should be a different kind of error?
      $ TypeError
        ("Circular modules:"
        PP.<+> PP.hsep (PP.punctuate PP.comma $ fromModuleName . moduleName . fst <$> ms))
        Nothing
        mempty

compileBuiltins :: VIX (ModuleHeader, [Generate.GeneratedSubmodule])
compileBuiltins = do
  builtin1File <- liftIO $ getDataFileName "rts/Builtin1.vix"
  builtin2File <- liftIO $ getDataFileName "rts/Builtin2.vix"
  let files = [builtin1File, builtin2File]
  moduleResults <- liftIO $ forM files $ \sourceFile ->
    Parse.parseFromFileEx Parse.modul sourceFile
  case sequence moduleResults of
    Failure es -> internalError
      $ "Error while processing builtin module:"
      <> PP.line <> PP.vcat (pretty <$> es)
    Success [builtins1, builtins2] -> do
      tgt <- getTarget
      let env = Builtin.environment tgt
      let builtinDefNames = HashSet.fromMap $ void env
          builtinConstrNames = HashSet.fromList
            [ QConstr n c
            | (n, (_, ClosedDefinition (DataDefinition d _), _)) <- HashMap.toList env
            , c <- constrNames d
            ]
      addModule "Sixten.Builtin" builtinConstrNames builtinDefNames
      addEnvironment env
      builtinResults1 <- File.process builtins1
      let envList = (\(n, (loc, d, t)) -> (n, loc, d, t)) <$> HashMap.toList env
      envResults <- File.backend envList
      addConvertedSignatures $ Builtin.convertedSignatures tgt
      convertedResults <- File.processConvertedGroup $ HashMap.toList $ Builtin.convertedEnvironment tgt
      builtinResults2 <- File.process builtins2
      let results = builtinResults1 <> envResults <> convertedResults <> builtinResults2
      return (ModuleHeader "Sixten.Builtin" AllExposed mempty, results)
    Success _ -> internalError "processBuiltins wrong number of builtins"

writeModules
  :: FilePath
  -> [(ModuleHeader, [Generate.GeneratedSubmodule])]
  -> VIX ProcessFilesResult
writeModules asmDir modules = do
  results <- forM modules $ \(moduleHeader, subModules) -> do
    let fileBase = asmDir </> fromModuleName (moduleName moduleHeader)
        llName = fileBase <> ".ll"
        cName = fileBase <> ".c"
    externs <- File.writeModule moduleHeader subModules llName [(C, cName)]
    return ProcessFilesResult
      { externFiles = externs
      , llFiles = [llName]
      }
  return $ mconcat results
