{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Command.Check where

import Protolude

import Data.IORef
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Time.Clock (NominalDiffTime)
import Options.Applicative as Options
import System.Directory
import System.FilePath
import System.FSNotify
import Util

import qualified Backend.Target as Target
import Command.Check.Options
import qualified Driver
import Effect.Log
import Error

optionsParserInfo :: ParserInfo Options
optionsParserInfo = info (helper <*> optionsParser)
  $ fullDesc
  <> progDesc "Type check a Sixten program"
  <> header "sixten check"

optionsParser :: Parser Options
optionsParser = Options
  <$> many (strArgument
    $ metavar "FILES..."
    <> help "Input source FILES or directories"
    <> action "file"
    )
  <*> many (strOption
    (long "verbose"
    <> short 'v'
    <> metavar "PREFIX"
    <> help "Log categories that start with PREFIX"
    <> completeWith
      [ "tc"
      , "tc.whnf"
      , "tc.unify"
      , "tc.subtype"
      , "tc.metavar"
      , "forall"
      , "tc.def"
      , "tc.gen"
      ]
    ))
  <*> optional (strOption
    $ long "log-file"
    <> metavar "FILE"
    <> help "Write logs to FILE instead of standard output"
    <> action "file"
    )
  <*> switch (
       long "watch"
    <> help "Watch the files for any changes, re-typechecking as needed."
    )

check :: Options -> IO ()
check opts = if watch opts then checkWatch opts else join (checkSimple opts)

checkWatch :: Options -> IO ()
checkWatch opts = do
  (dirs, initialFiles) <- splitDirsAndFiles (inputFiles opts)
  _exit <- checkSimple opts
  presentFiles <- newIORef (Set.fromList initialFiles)
  let recompile ev = do
        print ev
        files <- readIORef presentFiles
        void $ checkSimple opts {inputFiles = dirs ++ Set.toList files}
      myWatchDir wm dir = watchTree wm dir isVixFile recompile
      myWatchFile wm file = do
        absFile <- canonicalizePath file
        print absFile
        watchDir wm (takeDirectory absFile) isVixFile $ \event ->
          when (eventPath event == absFile) $ do
            case event of
              Added{}    -> modifyIORef presentFiles (Set.insert file)
              Modified{} -> pure ()
              Removed{}  -> modifyIORef presentFiles (Set.delete file)
              Unknown{}  -> pure ()
            recompile event
  withManagerConf watchConfig $ \wm -> do
    mapM_ (myWatchDir wm) dirs
    mapM_ (myWatchFile wm) initialFiles
    forever (threadDelay oneSecond)
  where
    watchConfig = defaultConfig{confDebounce = Debounce fiftyMillis}
    fiftyMillis = 0.050 :: NominalDiffTime
    oneSecond = 1000000
    isVixFile = (== ".vix") . takeExtension . eventPath
    splitDirsAndFiles ps = do
      (ds, fs) <- mapAndUnzipM (\p -> do
                                   isDir <- doesDirectoryExist p
                                   pure $ if isDir then (Just p, Nothing)
                                          else (Nothing, Just p)) ps
      pure (catMaybes ds, catMaybes fs)

checkSimple
  :: Options
  -> IO (IO ())
checkSimple opts = withLogHandle (logFile opts) $ \logHandle -> do
  sourceFiles <- flattenDirectories $ inputFiles opts
  errors <- Driver.checkFiles Driver.Arguments
    { Driver.sourceFiles = sourceFiles
    , Driver.readSourceFile = readFile
    , Driver.target = Target.defaultTarget
    , Driver.logHandle = logHandle
    , Driver.logCategories = \(Category c) ->
      any (`Text.isPrefixOf` c) (logPrefixes opts)
    , Driver.silentErrors = False
    }
  case errors of
    [] -> do
      putText "Type checking completed successfully"
      pure exitSuccess
    _ -> do
      mapM_ printError errors
      putText "Type checking failed"
      pure exitFailure
  where
    withLogHandle Nothing k = k stdout
    withLogHandle (Just file) k = Util.withFile file WriteMode k

command :: ParserInfo (IO ())
command = Command.Check.check <$> optionsParserInfo

flattenDirectories
  :: [FilePath]
  -> IO [FilePath]
flattenDirectories paths =
  concat <$> mapM flattenDirectory paths

flattenDirectory
  :: FilePath
  -> IO [FilePath]
flattenDirectory path = do
  isDir <- doesDirectoryExist path
  if isDir then
    listDirectoryRecursive path $ (== ".vix") . takeExtension
  else
    return [path]

listDirectoryRecursive :: FilePath -> (FilePath -> Bool) -> IO [FilePath]
listDirectoryRecursive dir p = do
  files <- listDirectory dir
  fmap concat $ forM files $ \file -> do
    let path = dir </> file
    isDir <- doesDirectoryExist path
    if isDir then
      listDirectoryRecursive path p
    else
      return [path | p path]
