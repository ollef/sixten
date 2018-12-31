module Command.Check.Options where

import Protolude

data Options = Options
  { inputFiles :: [FilePath]
  , logPrefixes :: [Text]
  , logFile :: Maybe FilePath
  } deriving (Show)
