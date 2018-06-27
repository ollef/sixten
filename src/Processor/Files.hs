{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Processor.Files where

import Control.Monad.Except
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.List.NonEmpty(NonEmpty)
import Data.Semigroup
import qualified Data.Text.Prettyprint.Doc as PP
import GHC.IO.Handle
import System.FilePath

import qualified Backend.Generate as Generate
import Backend.Target
import qualified Builtin
import Paths_sixten(getDataFileName)
import qualified Processor.File as File
import Processor.Result
import Syntax
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
  -> IO (Result [Module (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition))])
parseFiles srcFiles = do
  moduleResults <- forM srcFiles $ \sourceFile -> do
    parseResult <- File.parse sourceFile
    return $ fmap (:[]) $ File.dupCheck =<< parseResult
  return $ sconcat moduleResults

checkFiles :: Arguments -> IO (Result [Error])
checkFiles args = do
  parseResult <- parseFiles $ sourceFiles args
  fmap join $ forM parseResult $ \modules -> do
    let go = do
          _ <- compileBuiltins -- Done only for the side effects
          orderedModules <- cycleCheck modules
          mapM_ (File.frontend $ const $ return []) orderedModules
    fmap snd <$> runVIX go (target args) (logHandle args) (verbosity args) (silentErrors args)

processFiles :: Arguments -> IO (Result (ProcessFilesResult, [Error]))
processFiles args = do
  parseResult <- parseFiles $ sourceFiles args
  fmap join $ forM parseResult $ \modules -> do
    let go = do
          builtins <- compileBuiltins
          orderedModules <- cycleCheck modules
          compiledModules <- forM orderedModules $ \modul -> do
            compiledModule <- File.process modul
            return $ const compiledModule <$> modul
          writeModules (assemblyDir args) $ builtins : compiledModules
    runVIX go (target args) (logHandle args) (verbosity args) (silentErrors args)

cycleCheck
  :: (Functor t, Foldable t, MonadError Error m)
  => t (Module contents)
  -> m [Module contents]
cycleCheck modules = do
  let orderedModules = moduleDependencyOrder modules
  forM orderedModules $ \moduleGroup -> case moduleGroup of
    AcyclicSCC modul -> return modul
    CyclicSCC ms -> throwError
      -- TODO: Could be allowed?
      -- TODO: Maybe this should be a different kind of error?
      $ TypeError
        ("Circular modules:"
        PP.<+> PP.hsep (PP.punctuate PP.comma $ fromModuleName . moduleName <$> ms))
        Nothing
        mempty

compileBuiltins :: VIX (Module [Generate.GeneratedSubmodule])
compileBuiltins = do
  builtin1File <- liftIO $ getDataFileName "rts/Builtin1.vix"
  builtin2File <- liftIO $ getDataFileName "rts/Builtin2.vix"
  let files = [builtin1File, builtin2File]
  moduleResults <- liftIO $ forM files $ \sourceFile -> do
    parseResult <- File.parse sourceFile
    return $ File.dupCheck =<< parseResult
  case sequence moduleResults of
    Failure es -> internalError
      $ "Error while processing builtin module:"
      <> PP.line <> PP.vcat (pretty <$> es)
    Success [builtins1, builtins2] -> do
      tgt <- getTarget
      let context = Builtin.context tgt
      let builtinDefNames = HashSet.fromMap $ void context
          builtinConstrNames = HashSet.fromList
            [ QConstr n c
            | (n, (DataDefinition d _, _)) <- HashMap.toList context
            , c <- constrNames d
            ]
      addModule "Sixten.Builtin" builtinConstrNames builtinDefNames
      addContext context
      builtinResults1 <- File.process builtins1
      let contextList = (\(n, (d, t)) -> (n, d, t)) <$> HashMap.toList context
      contextResults <- File.backend contextList
      addConvertedSignatures $ Builtin.convertedSignatures tgt
      convertedResults <- File.processConvertedGroup $ HashMap.toList $ Builtin.convertedContext tgt
      builtinResults2 <- File.process builtins2
      let results = builtinResults1 <> contextResults <> convertedResults <> builtinResults2
      return $ Module "Sixten.Builtin" AllExposed mempty results
    Success _ -> internalError "processBuiltins wrong number of builtins"

writeModules
  :: FilePath
  -> [Module [Generate.GeneratedSubmodule]]
  -> VIX ProcessFilesResult
writeModules asmDir modules = do
  results <- forM modules $ \modul -> do
    let fileBase = asmDir </> fromModuleName (moduleName modul)
        llName = fileBase <> ".ll"
        cName = fileBase <> ".c"
    externs <- File.writeModule modul llName [(C, cName)]
    return ProcessFilesResult
      { externFiles = externs
      , llFiles = [llName]
      }
  return $ mconcat results
