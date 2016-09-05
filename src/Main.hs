{-# LANGUAGE OverloadedStrings #-}
module Main where

import Data.Maybe
import Options.Applicative

import qualified Processor

data Options = Options
  { inputFile :: FilePath
  , logFile :: Maybe FilePath
  , outputFile :: FilePath
  } deriving (Show)

cmdLineOptions :: ParserInfo Options
cmdLineOptions = info (helper <*> opts) $
  fullDesc
  <> progDesc "Compile a Sixten program"
  <> header "sixten"
  where
    opts = Options
      <$> argument str
        (metavar "FILE"
        <> help "Input source FILE"
        )
      <*> optional (strOption
        $ long "verbose"
        <> short 'v'
        <> metavar "FILE"
        <> help "Write log to FILE (default: 'log.txt')"
        )
      <*> strOption
        (long "output"
        <> short 'o'
        <> metavar "FILE"
        <> help "Write output to FILE"
        )

main :: IO ()
main = do
  opts <- execParser cmdLineOptions
  Processor.processFile
    (inputFile opts)
    (outputFile opts)
    (fromMaybe "log.txt" $ logFile opts)
