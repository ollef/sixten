{-# LANGUAGE OverloadedStrings #-}
module Command.Compile where

import Data.Monoid
import GHC.IO.Handle
import Options.Applicative
import System.Directory
import System.FilePath
import System.IO
import System.IO.Temp

import qualified Backend.Compile as Compile
import qualified Backend.Target as Target
import Command.Compile.Options
import qualified Processor.Error as Processor
import qualified Processor.Files as Processor

optionsParserInfo :: ParserInfo Options
optionsParserInfo = info (helper <*> optionsParser)
  $ fullDesc
  <> progDesc "Compile a Sixten program"
  <> header "sixten compile"

optionsParser :: Parser Options
optionsParser = Options
  <$> some (strArgument
    $ metavar "FILES..."
    <> help "Input source FILES"
    <> action "file"
    )
  <*> optional (strOption
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
  <*> option auto
    (long "verbose"
    <> short 'v'
    <> metavar "LEVEL"
    <> help "Set the verbosity level to LEVEL"
    <> value 0
    <> completeWith ["0", "10", "20", "30", "40"]
    )
  <*> optional (strOption
    $ long "log-file"
    <> metavar "FILE"
    <> help "Write logs to FILE instead of standard output"
    <> action "file"
    )

compile
  :: Options
  -> (Processor.Error -> IO a)
  -> (FilePath -> IO a)
  -> IO a
compile opts onError onSuccess = case maybe (Right Target.defaultTarget) Target.findTarget $ target opts of
  Left err -> onError $ Processor.CommandLineError err
  Right tgt ->
    withAssemblyDir (assemblyDir opts) $ \asmDir ->
    withOutputFile firstInputFile (maybeOutputFile opts) $ \outputFile ->
    withLogHandle (logFile opts) $ \logHandle -> do
      let linkedLlFileName = asmDir </> firstInputFile <.> "linked" <.> "ll" -- TODO
      procResult <- Processor.processFiles Processor.Arguments
        { Processor.sourceFiles = inputFiles opts
        , Processor.assemblyDir = asmDir
        , Processor.target = tgt
        , Processor.logHandle = logHandle
        , Processor.verbosity = verbosity opts
        }
      case procResult of
        Processor.Error err -> onError err
        Processor.Success result -> do
          Compile.compile opts Compile.Arguments
            { Compile.cFiles = Processor.cFiles result
            , Compile.llFiles = Processor.llFiles result
            , Compile.linkedLlFileName = linkedLlFileName
            , Compile.target = tgt
            , Compile.outputFile = outputFile
            }
          onSuccess outputFile
  where
    -- TODO should use the main file instead
    firstInputFile = case inputFiles opts of
      x:_ -> x
      _ -> "unknown"

    withAssemblyDir Nothing k = withSystemTempDirectory "sixten" k
    withAssemblyDir (Just dir) k = do
      createDirectoryIfMissing True dir
      k dir
    withOutputFile inputFile Nothing k
      = withTempFile inputDir fileName $ \outputFile outputFileHandle -> do
        hClose outputFileHandle
        k outputFile
      where
        (inputDir, inputFileName) = splitFileName inputFile
        fileName = dropExtension inputFileName

    withOutputFile _ (Just o) k = k o
    withLogHandle Nothing k = k stdout
    withLogHandle (Just file) k = withFile file WriteMode k

command :: ParserInfo (IO ())
command = go <$> optionsParserInfo
  where
    go opts = compile opts Processor.printError (const $ return ())
