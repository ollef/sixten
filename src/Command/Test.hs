module Command.Test where

import Options.Applicative
import System.Exit
import System.Process

import qualified Command.Compile as Compile

data Options = Options
  { expectedOutputFile :: Maybe FilePath
  , shouldFail :: Bool
  , compileOptions :: Compile.Options
  } deriving (Show)

optionsParserInfo :: ParserInfo Options
optionsParserInfo = info (helper <*> optionsParser)
  $ fullDesc
  <> progDesc "Test a Sixten program"
  <> header "sixten test"

optionsParser :: Parser Options
optionsParser = Options
  <$> optional (strOption
    $ long "expected"
    <> short 'e'
    <> metavar "FILE"
    <> help "Compare output to the contents of FILE"
    )
  <*> switch
    (long "fail"
    <> short 'f'
    <> help "The program should fail to typecheck"
    )
  <*> Compile.optionsParser

test :: Options -> IO ()
test opts = Compile.compile (compileOptions opts) $ \f -> do
  -- TODO check shouldFail
  output <- readProcess f [] ""
  mexpectedOutput <- traverse readFile $ expectedOutputFile opts
  case mexpectedOutput of
    Nothing -> return ()
    Just expectedOutput
      | output == expectedOutput -> do
        putStrLn $ Compile.inputFile (compileOptions opts) ++ ": SUCCESS"
        exitSuccess
      | otherwise -> do
        putStrLn "FAILED"
        putStrLn "Expected:"
        putStrLn expectedOutput
        putStrLn "But got:"
        putStrLn output
        exitFailure

command :: ParserInfo (IO ())
command = test <$> optionsParserInfo
