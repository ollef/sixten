{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Command.Compile where

import Protolude hiding ((<.>))

import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc.Render.Terminal
import Options.Applicative

import qualified Backend.Target as Target
import qualified Command.Check as Check
import qualified Command.Check.Options as Check
import Command.Compile.Options
import qualified Driver
import Driver.Query
import Effect.Log
import Error
import Util

optionsParserInfo :: ParserInfo (Check.Options, Options)
optionsParserInfo = info (helper <*> optionsParser)
  $ fullDesc
  <> progDesc "Compile a Sixten program"
  <> header "sixten compile"

optionsParser :: Parser (Check.Options, Options)
optionsParser = (,)
  <$> Check.optionsParser
  <*> (Options
    <$> optional (strOption
      $ long "output"
      <> short 'o'
      <> metavar "FILE"
      <> help "Write output to FILE"
      <> action "file"
      )
    <*> optional (strOption
      $ long "target"
      <> short 't'
      <> metavar "TARGET"
      <> help "Compile for CPU architecture TARGET"
      <> completeWith Target.architectures
      )
    <*> optional (strOption
      $ long "optimise"
      <> short 'O'
      <> metavar "LEVEL"
      <> help "Set the optimisation level to LEVEL"
      <> completeWith ["0", "1", "2", "3"]
      )
    <*> optional (strOption
      $ long "save-assembly"
      <> short 'S'
      <> metavar "DIR"
      <> help "Save intermediate assembly files to DIR"
      <> action "directory"
      )
    <*> optional (strOption
      $ long "llvm-config"
      <> metavar "PATH"
      <> help "Path to the llvm-config binary."
      <> action "file"
      )
    <*> many (strOption
      $ long "extra-lib-dir"
      <> metavar "DIR"
      <> help "Path where extra libraries (gc-lib.lib, etc.) exist."
      <> action "directory"
      )
    )

compile
  :: Check.Options
  -> Options
  -> (Error -> Task Query ())
  -> (Maybe FilePath -> IO k)
  -> IO k
compile checkOpts opts onError onResult =
  withLogHandle (Check.logFile checkOpts) $ \logHandle -> do
    let
      args sourceFiles tgt = Driver.Arguments
        { Driver.sourceFiles = sourceFiles
        , Driver.readSourceFile = readFile
        , Driver.target = tgt
        , Driver.logHandle = logHandle
        , Driver.logCategories = \(Category c) ->
          any (`Text.isPrefixOf` c) (Check.logPrefixes checkOpts)
        , Driver.onError = onError
        }
    case maybe (Right Target.defaultTarget) Target.findTarget $ target opts of
      Left err -> do
        Driver.execute
          (args mempty Target.defaultTarget)
          $ onError err
        onResult Nothing
      Right tgt -> do
        sourceFiles <- Check.flattenDirectories $ Check.inputFiles checkOpts
        Driver.compileFiles
          opts
          (args sourceFiles tgt)
          $ onResult . Just
  where
    withLogHandle Nothing k = k stdout
    withLogHandle (Just file) k = Util.withFile file WriteMode k

command :: ParserInfo (IO ())
command = go <$> optionsParserInfo
  where
    go (checkOpts, opts) = do
      anyErrorsVar <- newMVar False
      let
        onError err = do
          perr <- prettyError err
          liftIO $ modifyMVar_ anyErrorsVar $ \_ -> do
            putDoc perr
            return True
      compile checkOpts opts onError $ \mfp -> do
        anyErrors <- readMVar anyErrorsVar
        case (anyErrors, mfp) of
          (False, Just _) -> exitSuccess
          _ -> exitFailure
