{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
module Driver where

import Protolude hiding (state)

import Data.Dependent.Map(DMap)
import qualified Data.Dependent.Map as DMap
import qualified Data.Text.IO as Text
import Rock
import System.Directory
import System.IO(hClose)
import System.IO.Temp

import Backend.Target as Target
import qualified Command.Compile.Options as Compile
import Driver.Query
import Driver.Rules
import Effect
import Error
import Syntax

data Arguments = Arguments
  { sourceFiles :: [FilePath]
  , readSourceFile :: !(FilePath -> IO Text)
  , target :: !Target
  , logHandle :: !Handle
  , logCategories :: !(Category -> Bool)
  , onError :: !(Error -> IO ())
  }

execute :: Arguments -> Task Query a -> IO a
execute args task = do
  startedVar <- newMVar mempty
  printVar <- newMVar 0
  let
    logEnv_ = LogEnv
      { _logCategories = Driver.logCategories args
      , _logAction = Text.hPutStrLn $ logHandle args
      }
    traceFetch_ :: Rules Query -> Rules Query
    traceFetch_ =
      if _logCategories logEnv_ "fetch" then
        traceFetch
          (\key -> modifyMVar_ printVar $ \n -> do
            _logAction logEnv_ $ fold (replicate n "| ") <> "fetching " <> show key
            return $ n + 1)
          (\_ _ -> modifyMVar_ printVar $ \n -> do
            _logAction logEnv_ $ fold (replicate (n - 1) "| ") <> "*"
            return $ n - 1)
        else
          identity
    writeErrors _ errs =
      forM_ errs $ onError args
    tasks
      = memoise startedVar
      $ traceFetch_
      $ writer writeErrors
      $ rules logEnv_ (sourceFiles args) (readSourceFile args) (target args)
  runTask sequentially tasks task

checkFiles
  :: Arguments
  -> IO ()
checkFiles args = void $ execute args $ fetch CheckAll

data CompileResult = CompileResult
  { externFiles :: [(Language, FilePath)]
  , llFiles :: [FilePath]
  }

compileFiles
  :: Compile.Options
  -> Arguments
  -> (FilePath -> IO a)
  -> IO a
compileFiles opts args k =
  withOutputFile (Compile.maybeOutputFile opts) $ \outputFile -> do
    execute args $ fetch $ CompileAll outputFile opts
    k outputFile
  where
    withOutputFile Nothing k'
      = withTempFile "." "temp.exe" $ \outputFile outputFileHandle -> do
        hClose outputFileHandle
        k' outputFile
    withOutputFile (Just o) k' = do
      o' <- makeAbsolute o
      k' o'

-------------------------------------------------------------------------------
-- Incremental execution
data DriverState = DriverState
  { _tracesVar :: !(MVar (Traces Query))
  , _errorsVar :: !(MVar (DMap Query (Const [Error])))
  }

initialState :: IO DriverState
initialState = do
  tracesVar <- newMVar mempty
  errorsVar <- newMVar mempty
  return DriverState
    { _tracesVar = tracesVar
    , _errorsVar = errorsVar
    }

incrementallyExecuteVirtualFile
  :: DriverState
  -> FilePath
  -> Text
  -> Task Query a
  -> IO (a, [Error])
incrementallyExecuteVirtualFile state file text task = do
  startedVar <- newMVar mempty
  printVar <- newMVar 0
  let
    readSourceFile_ file'
      | file == file' = return text
      | otherwise = readFile file'
    logEnv_ = LogEnv
      { _logCategories = (==) "fetch"
      , _logAction = Text.hPutStrLn stderr
      }
    traceFetch_ :: Rules Query -> Rules Query
    traceFetch_ =
      if _logCategories logEnv_ "fetch" then
        traceFetch
          (\key -> modifyMVar_ printVar $ \n -> do
            _logAction logEnv_ $ fold (replicate n "| ") <> "fetching " <> show key
            return $ n + 1)
          (\_ _ -> modifyMVar_ printVar $ \n -> do
            _logAction logEnv_ $ fold (replicate (n - 1) "| ") <> "*"
            return $ n - 1)
        else
          identity
    writeErrors key errs = do
      Text.hPutStrLn stderr $ "writeErrors " <> show key <> " " <> show (pretty errs)
      modifyMVar_ (_errorsVar state) $
        pure . DMap.insert key (Const errs)
    tasks
      = memoise startedVar
      $ verifyTraces (_tracesVar state)
      $ traceFetch_
      $ writer writeErrors
      $ rules logEnv_ (pure file) readSourceFile_ Target.defaultTarget
  result <- runTask sequentially tasks task
  started <- readMVar startedVar
  modifyMVar_ (_tracesVar state) $
    pure . DMap.intersectionWithKey (\_ _ t -> t) started
  errorsMap <- modifyMVar (_errorsVar state) $ \errors -> do
    let
      errors' = DMap.intersectionWithKey (\_ _ e -> e) started errors
    return (errors', errors')
  let
    errors = do
      (_ DMap.:=> Const errs) <- DMap.toList errorsMap
      errs
  Text.hPutStrLn stderr $ "all errors length " <> show (DMap.size errorsMap)
  Text.hPutStrLn stderr $ "all errors " <> show (pretty errors)
  return (result, errors)
