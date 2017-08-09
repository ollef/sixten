module Processor.Files where

import GHC.IO.Handle

import Backend.Target
import Processor.Error

data Arguments = Arguments
  { sourceFiles :: [FilePath]
  , assemblyDir :: !FilePath
  , target :: !Target
  , logHandle :: !Handle
  , verbosity :: !Int
  } deriving (Eq, Show)

data ProcessFilesResult = ProcessFilesResult
  { cFiles :: [FilePath]
  , llFiles :: [FilePath]
  }

processFiles :: Arguments -> IO (Result ProcessFilesResult)
processFiles args = undefined -- TODO
