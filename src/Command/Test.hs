{-# LANGUAGE OverloadedStrings #-}
module Command.Test where

import Data.Foldable
import Data.List
import Data.Monoid
import Options.Applicative
import System.Exit
import System.Process

import qualified Command.Check.Options as Check
import qualified Command.Compile as Compile
import qualified Command.Compile.Options as Compile
import qualified Processor.Result as Processor

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
    onCompileError errs = case errs of
      Processor.SyntaxError _:_
        | expectSyntaxError opts -> success
        | otherwise -> failed "No syntax error" $ mapM_ Processor.printError errs
      Processor.TypeError _:_
        | expectTypeError opts -> success
        | otherwise -> failed "No type error" $ mapM_ Processor.printError errs
      Processor.CommandLineError _:_
        -> failed "No command-line error" $ mapM_ Processor.printError errs
      [] -> failed "No unknown error" (return ())
    onCompileSuccess f
      | expectSyntaxError opts = failed "Syntax error" $ putStrLn "Successful compilation"
      | expectTypeError opts = failed "Type error" $ putStrLn "Successful compilation"
      | otherwise = do
      output <- readProcess f [] ""
      mexpectedOutput <- traverse readFile $ expectedOutputFile opts
      case mexpectedOutput of
        Nothing -> success
        Just expectedOutput
          | output == expectedOutput -> success
          | otherwise -> failed expectedOutput $ putStrLn output
    success = do
      putStrLn $ "OK: " ++ intercalate ", " (toList . Check.inputFiles . Compile.checkOptions . compileOptions $ opts)
      exitSuccess
    failed expected actual = do
      putStrLn $ "FAILED: " ++ intercalate ", " (toList . Check.inputFiles . Compile.checkOptions . compileOptions $ opts)
      putStrLn "Expected:"
      putStrLn expected
      putStrLn "But got:"
      () <- actual
      exitFailure

command :: ParserInfo (IO ())
command = test <$> optionsParserInfo
