module Command.Check.Options where

import Data.List.NonEmpty(NonEmpty)

data Options = Options
  { inputFiles :: NonEmpty FilePath
  , verbosity :: Int
  , logFile :: Maybe FilePath
  } deriving (Show)
