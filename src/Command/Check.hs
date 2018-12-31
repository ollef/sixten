{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Command.Check where

import Protolude

import qualified Data.Text as Text
import Options.Applicative as Options
import System.Directory
import System.FilePath
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

check
  :: Options
  -> IO ()
check opts = withLogHandle (logFile opts) $ \logHandle -> do
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
      exitSuccess
    _ -> do
      mapM_ printError errors
      putText "Type checking failed"
      exitFailure
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
