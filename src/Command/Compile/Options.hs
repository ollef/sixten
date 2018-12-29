module Command.Compile.Options where

import Prelude(String)
import Protolude

data Options = Options
  { maybeOutputFile :: Maybe FilePath
  , target :: Maybe String
  , optimisation :: Maybe String
  , assemblyDir :: Maybe FilePath
  , llvmConfig :: Maybe FilePath
  , extraLibDir :: [FilePath]
  } deriving (Eq, Ord, Show)
