module Command.Test where

import Options.Applicative
import System.Exit
import System.Process

import qualified Command.Run as Run

data Options = Options
  { inputFile :: FilePath
  , expectedOutputFile :: FilePath
  } deriving (Show)

testOptionsParser :: ParserInfo Options
testOptionsParser = info (helper <*> opts)
  $ fullDesc
  <> progDesc "Test a Sixten program"
  <> header "sixten test"
  where
    opts = Options
      <$> argument str
        (metavar "FILE"
        <> help "Input source FILE"
        )
      <*> strOption 
        (long "expected"
        <> short 'e'
        <> metavar "FILE"
        <> help "Compare output to contents of FILE"
        )

test :: Options -> IO ()
test o = do
  output <- Run.run (\f -> readProcess f [] "") Run.Options
    { Run.inputFile = inputFile o
    }
  expectedOutput <- readFile $ expectedOutputFile o
  if output == expectedOutput
  then do
    putStrLn $ inputFile o ++ ": SUCCESS"
    exitSuccess
  else do
    putStrLn "FAILED"
    putStrLn "Expected:"
    putStrLn expectedOutput
    putStrLn "But got:"
    putStrLn output
    exitFailure

command :: ParserInfo (IO ())
command = test <$> testOptionsParser
