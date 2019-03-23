{-# LANGUAGE LambdaCase #-}
module Command.Run where

import Prelude(String, words)
import Protolude

import Options.Applicative
import System.Process

import qualified Command.Check.Options as Check
import qualified Command.Compile as Compile
import qualified Command.Compile.Options as Compile
import Error

data Options = Options
  { checkOptions :: Check.Options
  , compileOptions :: Compile.Options
  , commandLineArguments :: Maybe String
  } deriving (Show)

optionsParserInfo :: ParserInfo Options
optionsParserInfo = info (helper <*> optionsParser)
  $ fullDesc
  <> progDesc "Run a Sixten program"
  <> header "sixten run"

optionsParser :: Parser Options
optionsParser = uncurry Options
  <$> Compile.optionsParser
  <*> optional (strOption
    $ long "args"
    <> metavar "ARGS"
    <> help "Command-line options passed to the Sixten program"
    )

run :: Options -> IO ()
run opts = do
  anyErrorsVar <- newMVar False
  let
    onError err =
      modifyMVar_ anyErrorsVar $ \_ -> do
        printError err
        return True
  Compile.compile (checkOptions opts) (compileOptions opts) onError $ \case
    Nothing -> exitFailure
    Just fp -> callProcess fp $ maybe [] words $ commandLineArguments opts

command :: ParserInfo (IO ())
command = run <$> optionsParserInfo
