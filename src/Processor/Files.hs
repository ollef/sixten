{-# LANGUAGE OverloadedStrings #-}
module Processor.Files where

import Control.Monad.Except
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.List
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty(NonEmpty)
import Data.Semigroup
import Data.Text(Text)
import qualified Data.Text as Text
import GHC.IO.Handle
import System.FilePath

import qualified Backend.Generate as Generate
import Backend.Target
import qualified Builtin
import Paths_sixten(getDataFileName)
import qualified Processor.File as File
import Processor.Result
import Syntax
import qualified Syntax.Concrete.Unscoped as Unscoped
import qualified Syntax.Sized.Extracted as Extracted
import VIX

data Arguments = Arguments
  { sourceFiles :: NonEmpty FilePath
  , assemblyDir :: !FilePath
  , target :: !Target
  , logHandle :: !Handle
  , verbosity :: !Int
  } deriving (Eq, Show)

data ProcessFilesResult = ProcessFilesResult
  { externFiles :: [(Language, FilePath)]
  , llFiles :: [FilePath]
  }

instance Monoid ProcessFilesResult where
  mempty = ProcessFilesResult mempty mempty
  mappend (ProcessFilesResult c1 l1) (ProcessFilesResult c2 l2)
    = ProcessFilesResult (mappend c1 c2) (mappend l1 l2)

processFiles :: Arguments -> IO (Result ProcessFilesResult)
processFiles args = do
  builtin1File <- getDataFileName "rts/Builtin1.vix"
  builtin2File <- getDataFileName "rts/Builtin2.vix"
  let files = builtin1File NonEmpty.<| builtin2File NonEmpty.<| sourceFiles args
  moduleResults <- forM files $ \sourceFile -> do
    parseResult <- File.parse sourceFile
    return $ fmap (:[]) $ File.dupCheck =<< parseResult
  let modulesResult = sconcat moduleResults
  compiledModules <- fmap join $ forM modulesResult $ processModules args
  forM compiledModules $ writeModules $ assemblyDir args

processModules
  :: Arguments
  -> [Module (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition QName))]
  -> IO (Result [Module [Extracted.Submodule (Generate.Generated (Text, File.DependencySigs))]])
processModules args (builtins1 : builtins2 : modules) = do
  result <- runVIX go tgt (logHandle args) (verbosity args)
  return $ case result of
    Left err -> Failure $ pure $ TypeError $ Text.pack err
    Right res -> Success res
  where
    tgt = target args

    go = do
      builtins <- processBuiltins tgt builtins1 builtins2
      let builtinModule = Module "Sixten.Builtin" AllExposed mempty builtins
      let orderedModules = dependencyOrder modules
      results <- forM orderedModules $ \moduleGroup -> case moduleGroup of
        [modul] -> traverse (const $ (File.frontend >=> File.backend) modul) modul
        _ -> throwError -- TODO: Could be allowed?
          $ "Circular modules: " ++ intercalate ", " (fromModuleName . moduleName <$> moduleGroup)
      return $ builtinModule : results
processModules _ _ = error "processModules"

processBuiltins
  :: Target
  -> Module (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition QName))
  -> Module (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition QName))
  -> VIX [Extracted.Submodule (Generate.Generated (Text, File.DependencySigs))]
processBuiltins tgt builtins1 builtins2 = do
  let builtinDefNames = HashSet.fromMap $ void context
      builtinConstrNames = HashSet.fromList
        [ QConstr n c
        | (n, (DataDefinition d _, _)) <- HashMap.toList context
        , c <- constrNames d
        ]
  addModule "Sixten.Builtin" $ HashSet.map Right builtinDefNames <> HashSet.map Left builtinConstrNames
  addContext context
  builtinResults1 <- File.process builtins1
  let contextList = (\(n, (d, t)) -> (n, d, t)) <$> HashMap.toList context
  contextResults <- File.backend contextList
  addConvertedSignatures $ Builtin.convertedSignatures tgt
  convertedResults <- File.processConvertedGroup $ HashMap.toList $ Builtin.convertedContext tgt
  builtinResults2 <- File.process builtins2
  return $ builtinResults1 <> contextResults <> convertedResults <> builtinResults2
  where
    context = Builtin.context tgt

writeModules
  :: FilePath
  -> [Module [Extracted.Submodule (Generate.Generated (Text, File.DependencySigs))]]
  -> IO ProcessFilesResult
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
