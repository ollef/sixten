module Command.Run where

import Data.Monoid
import Options.Applicative
import System.Process

import qualified Command.Compile as Compile
import qualified Command.Compile.Options as Compile
import qualified Processor.Result as Processor

data Options = Options
  { compileOptions :: Compile.Options
  , commandLineArguments :: [String]
  } deriving (Show)

optionsParserInfo :: ParserInfo Options
optionsParserInfo = info (helper <*> optionsParser)
  $ fullDesc
  <> progDesc "Run a Sixten program"
  <> header "sixten run"

optionsParser :: Parser Options
optionsParser = Options
  <$> Compile.optionsParser
  <*> many
    (strArgument
    $ metavar "ARGS.."
    <> help "Command-line options passed to the Sixten program"
    )

run :: Options -> IO ()
run opts = Compile.compile (compileOptions opts) (mapM_ Processor.printError) $ \f ->
  callProcess f $ commandLineArguments opts

command :: ParserInfo (IO ())
command = run <$> optionsParserInfo
