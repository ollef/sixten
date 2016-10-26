module Command.Run where

import GHC.IO.Handle
import Options.Applicative
import System.FilePath
import System.IO.Temp
import System.Process

import qualified Command.Compile as Compile

data Options = Options
  { inputFile :: FilePath
  } deriving (Show)

runOptionsParser :: ParserInfo Options
runOptionsParser = info (helper <*> opts)
  $ fullDesc
  <> progDesc "Run a Sixten program"
  <> header "sixten run"
  where
    opts = Options
      <$> argument str
        (metavar "FILE"
        <> help "Input source FILE"
        )

run :: (FilePath -> IO a) -> Options -> IO a
run k o = do
  let (inputDir, inputFileName) = splitFileName $ inputFile o
      outputFileSuggestion = dropExtension inputFileName
  withTempFile inputDir outputFileSuggestion $ \outputFile outputFileHandle -> do
    hClose outputFileHandle
    Compile.compile Compile.Options
      { Compile.inputFile = inputFile o
      , Compile.outputFile = outputFile
      , Compile.optimisation = Nothing
      , Compile.assemblyDir = Nothing
      }
    k outputFile

command :: ParserInfo (IO ())
command = run (\f -> callProcess f []) <$> runOptionsParser
