{-# LANGUAGE OverloadedStrings #-}
module Command.Compile where

import GHC.IO.Handle
import Options.Applicative
import System.Directory
import System.FilePath
import System.IO
import System.IO.Temp
import System.Process

import qualified Backend.Target as Target
import qualified Processor

data Options = Options
  { inputFile :: FilePath
  , maybeOutputFile :: Maybe FilePath
  , target :: Maybe String
  , optimisation :: Maybe String
  , assemblyDir :: Maybe FilePath
  , verbosity :: Int
  , logFile :: Maybe FilePath
  } deriving (Show)

optionsParserInfo :: ParserInfo Options
optionsParserInfo = info (helper <*> optionsParser)
  $ fullDesc
  <> progDesc "Compile a Sixten program"
  <> header "sixten compile"

optionsParser :: Parser Options
optionsParser = Options
  <$> strArgument
    (metavar "FILE"
    <> help "Input source FILE"
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

compile :: Options -> (Processor.Error -> IO a) -> (FilePath -> IO a) -> IO a
compile opts onError onSuccess = case maybe (Right Target.defaultTarget) Target.findTarget $ target opts of
  Left err -> onError $ Processor.CommandLineError err
  Right tgt ->
    withAssemblyDir (assemblyDir opts) $ \asmDir ->
    withOutputFile (maybeOutputFile opts) $ \outputFile ->
    withLogHandle (logFile opts) $ \logHandle -> do
      let llFile = asmDir </> fileName <.> "ll"
      procResult <- Processor.processFile (inputFile opts) llFile tgt logHandle $ verbosity opts
      case procResult of
        Processor.Error err -> onError err
        Processor.Success -> do
          (optLlFile, optFlag) <- case optimisation opts of
            Nothing -> return (llFile, id)
            Just optLevel -> do
              let optFlag = ("-O" <> optLevel :)
                  optLlFile = asmDir </> fileName <> "-opt" <.> "ll"
              callProcess "opt" $ optFlag ["-S", llFile, "-o", optLlFile]
              return (optLlFile, optFlag)
          let asmFile = asmDir </> fileName <.> "s"
          callProcess "llc" $ optFlag ["-march=" <> Target.architecture tgt, optLlFile, "-o", asmFile]
          ldFlags <- readProcess "pkg-config" ["--libs", "--static", "bdw-gc"] ""
          callProcess "gcc" $ concatMap words (lines ldFlags) ++ optFlag [asmFile, "-o", outputFile]
          onSuccess outputFile
  where
    (inputDir, inputFileName) = splitFileName $ inputFile opts
    fileName = dropExtension inputFileName

    withAssemblyDir Nothing k = withSystemTempDirectory "sixten" k
    withAssemblyDir (Just dir) k = do
      createDirectoryIfMissing True dir
      k dir
    withOutputFile Nothing k
      = withTempFile inputDir fileName $ \outputFile outputFileHandle -> do
        hClose outputFileHandle
        k outputFile
    withOutputFile (Just o) k = k o
    withLogHandle Nothing k = k stdout
    withLogHandle (Just file) k = withFile file WriteMode k

command :: ParserInfo (IO ())
command = go <$> optionsParserInfo
  where
    go opts = compile opts Processor.printError (const $ return ())
