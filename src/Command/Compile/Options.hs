module Command.Compile.Options where

data Options = Options
  { inputFiles :: [FilePath]
  , maybeOutputFile :: Maybe FilePath
  , target :: Maybe String
  , optimisation :: Maybe String
  , assemblyDir :: Maybe FilePath
  , verbosity :: Int
  , logFile :: Maybe FilePath
  } deriving (Show)
