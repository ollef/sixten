{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
module Driver where

import Protolude

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
  , silentErrors :: !Bool
  }

execute :: Arguments -> Task Query a -> IO (a, [Error])
execute args task = do
  startedVar <- newMVar mempty
  errorsVar <- newMVar mempty
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
    writeErrors _ [] = return ()
    writeErrors key errs =
      modifyMVar_ errorsVar $ pure . DMap.insert key (Const errs)
    tasks
      = traceFetch_
      $ memoise startedVar
      $ writer writeErrors
      $ rules logEnv_ (sourceFiles args) (readSourceFile args) (target args)
  res <- runTask sequentially tasks task
  errorsMap <- readMVar errorsVar
  let
    errors = concat [errs | _ DMap.:=> Const errs <- DMap.toList errorsMap]
  return (res, errors)

checkFiles
  :: Arguments
  -> IO [Error]
checkFiles args = do
  (_, errors) <- execute args $ fetch CheckAll
  return errors

executeVirtualFile
  :: FilePath
  -> Text
  -> Task Query a
  -> IO (a, [Error])
executeVirtualFile file text = execute Arguments
  { sourceFiles = pure file
  , readSourceFile = \file' -> if file == file' then return text else readFile file'
  , target = Target.defaultTarget
  , logHandle = stdout
  , Driver.logCategories = const False
  , silentErrors = True
  }

data CompileResult = CompileResult
  { externFiles :: [(Language, FilePath)]
  , llFiles :: [FilePath]
  }

compileFiles
  :: Compile.Options
  -> Arguments
  -> (FilePath -> [Error] -> IO a)
  -> IO a
compileFiles opts args k =
  withOutputFile (Compile.maybeOutputFile opts) $ \outputFile -> do
    ((), errors) <- execute args $ fetch $ CompileAll outputFile opts
    k outputFile errors
  where
    withOutputFile Nothing k'
      = withTempFile "." "temp.exe" $ \outputFile outputFileHandle -> do
        hClose outputFileHandle
        k' outputFile
    withOutputFile (Just o) k' = do
      o' <- makeAbsolute o
      k' o'
