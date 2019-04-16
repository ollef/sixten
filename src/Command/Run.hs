{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
module Command.Run where

import Prelude(String, words)
import Protolude

import Data.Text.Prettyprint.Doc.Render.Terminal
import Options.Applicative
import System.Process

import qualified Command.Check.Options as Check
import qualified Command.Compile as Compile
import qualified Command.Compile.Options as Compile
import Driver.Query

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
    onError err = do
      perr <- prettyError err
      liftIO $ modifyMVar_ anyErrorsVar $ \_ -> do
        putDoc perr
        return True
  Compile.compile (checkOptions opts) (compileOptions opts) onError $ \case
    Nothing -> exitFailure
    Just fp -> callProcess fp $ maybe [] words $ commandLineArguments opts

command :: ParserInfo (IO ())
command = run <$> optionsParserInfo
