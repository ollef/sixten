module Command.Compile.Options where

import qualified Command.Check.Options as Check

data Options = Options
  { checkOptions :: Check.Options
  , maybeOutputFile :: Maybe FilePath
  , target :: Maybe String
  , optimisation :: Maybe String
  , assemblyDir :: Maybe FilePath
  , llvmConfig :: Maybe FilePath
  } deriving (Show)
