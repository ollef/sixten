{-# LANGUAGE OverloadedStrings #-}
module Processor.Files where

import Control.Monad.Except
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.List.NonEmpty as NonEmpty
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
import qualified Syntax.Concrete.Unscoped as Unscoped
import Util.TopoSort
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

checkFiles :: Arguments -> IO (Result ())
checkFiles
  = processFilesWith
  $ mapM (processModulesWith (File.frontend (const $ return [])))
    >=> return . void

processFiles :: Arguments -> IO (Result ProcessFilesResult)
processFiles args
  = processFilesWith (mapM (processModulesWith File.process)
  >=> mapM (writeModules $ assemblyDir args)) args

processFilesWith
  :: (Result [Module (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition))] -> VIX (Result a))
  -> Arguments
  -> IO (Result a)
processFilesWith f args = do
  builtin1File <- getDataFileName "rts/Builtin1.vix"
  builtin2File <- getDataFileName "rts/Builtin2.vix"
  let files = builtin1File NonEmpty.<| builtin2File NonEmpty.<| sourceFiles args
  moduleResults <- forM files $ \sourceFile -> do
    parseResult <- File.parse sourceFile
    return $ fmap (:[]) $ File.dupCheck =<< parseResult
  let modulesResult = sconcat moduleResults
  result <- runVIX (f modulesResult) (target args) (logHandle args) (verbosity args)
  return $ case result of
    Left err -> Failure $ pure err
    Right (Failure errs) -> Failure errs
    Right (Success res) -> Success res

processModulesWith
  :: (Module (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition)) -> VIX [Generate.GeneratedSubmodule])
  -> [Module (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition))]
  -> VIX [Module [Generate.GeneratedSubmodule]]
processModulesWith f (builtins1 : builtins2 : modules) = do
  builtins <- processBuiltins builtins1 builtins2
  let builtinModule = Module "Sixten.Builtin" AllExposed mempty builtins
  let orderedModules = moduleDependencyOrder modules
  results <- forM orderedModules $ \moduleGroup -> case moduleGroup of
    AcyclicSCC modul -> traverse (const $ f modul) modul
    CyclicSCC ms -> throwError
      -- TODO: Could be allowed?
      -- TODO: Maybe this should be a different kind of error?
      $ TypeError
        ("Circular modules:"
        PP.<+> PP.hsep (PP.punctuate PP.comma $ fromModuleName . moduleName <$> ms))
        Nothing
        mempty
  return $ builtinModule : results
processModulesWith _ _ = internalError "processModules"

processBuiltins
  :: Module (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition))
  -> Module (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition))
  -> VIX [Generate.GeneratedSubmodule]
processBuiltins builtins1 builtins2 = do
  tgt <- getTarget
  let context = Builtin.context tgt
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
