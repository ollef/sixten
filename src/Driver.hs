{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
module Driver where

import Protolude

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
      = traceFetch_
      $ memoise startedVar
      $ writer writeErrors
      $ rules logEnv_ (sourceFiles args) (readSourceFile args) (target args)
  runTask sequentially tasks task

checkFiles
  :: Arguments
  -> IO ()
checkFiles args = void $ execute args $ fetch CheckAll

executeVirtualFile
  :: FilePath
  -> Text
  -> (Error -> IO ())
  -> Task Query a
  -> IO a
executeVirtualFile file text onError_ = execute Arguments
  { sourceFiles = pure file
  , readSourceFile = \file' -> if file == file' then return text else readFile file'
  , target = Target.defaultTarget
  , logHandle = stdout
  , Driver.logCategories = const False
  , onError = onError_
  }

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
