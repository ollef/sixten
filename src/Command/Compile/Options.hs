module Command.Compile.Options where

import Data.List.NonEmpty(NonEmpty)

data Options = Options
  { inputFiles :: NonEmpty FilePath
  , maybeOutputFile :: Maybe FilePath
  , target :: Maybe String
  , optimisation :: Maybe String
  , assemblyDir :: Maybe FilePath
  , verbosity :: Int
  , logFile :: Maybe FilePath
  , llvmConfig :: Maybe FilePath
  } deriving (Show)
