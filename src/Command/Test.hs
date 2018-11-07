{-# LANGUAGE OverloadedStrings #-}
module Command.Test where

import Protolude hiding (TypeError)

import qualified Data.Text as Text
import Options.Applicative
import System.Process

import qualified Command.Check.Options as Check
import qualified Command.Compile as Compile
import qualified Command.Compile.Options as Compile
import Error

data Options = Options
  { checkOptions :: Check.Options
  , compileOptions :: Compile.Options
  , expectedOutputFile :: Maybe FilePath
  , expectTypeError :: Bool
  , expectSyntaxError :: Bool
  } deriving (Show)

optionsParserInfo :: ParserInfo Options
optionsParserInfo = info (helper <*> optionsParser)
  $ fullDesc
  <> progDesc "Test a Sixten program"
  <> header "sixten test"

optionsParser :: Parser Options
optionsParser = uncurry Options
  <$> Compile.optionsParser
  <*> optional (strOption
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

test :: Options -> IO ()
test opts = Compile.compile (checkOptions opts) (compileOptions opts) True $ \mfp errs ->
  case (mfp, errs) of
    (Just fp, []) -> onCompileSuccess fp
    _ -> onCompileError errs
  where
    onCompileError errs = case errs of
      SyntaxError {}:_
        | expectSyntaxError opts -> success
        | otherwise -> failed "No syntax error" $ mapM_ printError errs
      TypeError {}:_
        | expectTypeError opts -> success
        | otherwise -> failed "No type error" $ mapM_ printError errs
      CommandLineError {}:_
        -> failed "No command-line error" $ mapM_ printError errs
      InternalError {}:_
        -> failed "No internal error" $ mapM_ printError errs
      [] -> failed "No unknown error" (return ())
    onCompileSuccess f
      | expectSyntaxError opts = failed "Syntax error" $ putText "Successful compilation"
      | expectTypeError opts = failed "Type error" $ putText "Successful compilation"
      | otherwise = do
      output <- readProcess f [] ""
      mexpectedOutput <- traverse readFile $ expectedOutputFile opts
      case mexpectedOutput of
        Nothing -> success
        Just expectedOutput
          | Text.pack output == expectedOutput -> success
          | otherwise -> failed expectedOutput $ putStrLn output
    success = do
      putStrLn $ "OK: " ++ intercalate ", " (toList . Check.inputFiles . checkOptions $ opts)
      exitSuccess
    failed expected actual = do
      putStrLn $ "FAILED: " ++ intercalate ", " (toList . Check.inputFiles . checkOptions $ opts)
      putText "Expected:"
      putText expected
      putText "But got:"
      () <- actual
      exitFailure

command :: ParserInfo (IO ())
command = test <$> optionsParserInfo
