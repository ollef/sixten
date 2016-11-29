module Command.Test where

import Options.Applicative
import System.Exit
import System.Process

import qualified Command.Compile as Compile
import qualified Processor

data Options = Options
  { expectedOutputFile :: Maybe FilePath
  , expectTypeError :: Bool
  , expectSyntaxError :: Bool
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
    <> action "file"
    )
  <*> switch
    (long "expect-type-error"
    <> help "The program should fail to typecheck"
    )
  <*> switch
    (long "expect-syntax-error"
    <> help "The program should yield a syntax error"
    )
  <*> Compile.optionsParser

test :: Options -> IO ()
test opts = Compile.compile (compileOptions opts) onCompileError onCompileSuccess
  where
    onCompileError err = case err of
      Processor.SyntaxError _
        | expectSyntaxError opts -> success
        | otherwise -> failed "No syntax error" $ Processor.printError err
      Processor.ResolveError _
        | expectSyntaxError opts -> success
        | otherwise -> failed "No syntax error" $ Processor.printError err
      Processor.TypeError _
        | expectTypeError opts -> success
        | otherwise -> failed "No type error" $ Processor.printError err
    onCompileSuccess f
      | expectSyntaxError opts = failed "Syntax error" $ putStrLn "Successful compilation"
      | expectTypeError opts = failed "Type error" $ putStrLn "Successful compilation"
      | otherwise = do
      output <- readProcess f [] ""
      mexpectedOutput <- traverse readFile $ expectedOutputFile opts
      case mexpectedOutput of
        Nothing -> return ()
        Just expectedOutput
          | output == expectedOutput -> success
          | otherwise -> failed expectedOutput $ putStrLn output
    success = do
      putStrLn $ Compile.inputFile (compileOptions opts) ++ ": SUCCESS"
      exitSuccess
    failed expected actual = do
      putStrLn $ Compile.inputFile (compileOptions opts) ++ ": FAILED"
      putStrLn "Expected:"
      putStrLn expected
      putStrLn "But got:"
      () <- actual
      exitFailure

command :: ParserInfo (IO ())
command = test <$> optionsParserInfo