{-# LANGUAGE OverloadedStrings #-}
module Main where

import Options.Applicative
import System.Directory
import System.FilePath
import System.IO.Temp
import System.Process

import qualified Processor

data Options = Options
  { inputFile :: FilePath
  , outputFile :: FilePath
  , optimisation :: Maybe String
  , assemblyDir :: Maybe FilePath
  } deriving (Show)

cmdLineOptions :: ParserInfo Options
cmdLineOptions = info (helper <*> opts)
  $ fullDesc
  <> progDesc "Compile a Sixten program"
  <> header "sixten"
  where
    opts = Options
      <$> argument str
        (metavar "FILE"
        <> help "Input source FILE"
        )
      <*> strOption
        (long "output"
        <> short 'o'
        <> metavar "FILE"
        <> help "Write output to FILE"
        )
      <*> optional (strOption
        $ long "optimisation-level"
        <> short 'O'
        <> metavar "LEVEL"
        <> help "Set the optimisation level to LEVEL"
        )
      <*> optional (strOption
        $ long "save-assembly"
        <> short 'S'
        <> metavar "DIR"
        <> help "Save intermediate assembly files to DIR"
        )

main :: IO ()
main = do
  opts <- execParser cmdLineOptions
  withAssemblyDir (assemblyDir opts) $ \asmDir -> do
    let inFile = inputFile opts
        fileName = dropExtension $ takeFileName inFile
        llFile = asmDir </> fileName <.> "ll"
        logFile = asmDir </> fileName <> "-log.txt"
    Processor.processFile inFile llFile logFile
    (optLlFile, optFlag) <- case optimisation opts of
      Nothing -> return (llFile, id)
      Just optLevel -> do
        let optFlag = ("-O" <> optLevel :)
            optLlFile = asmDir </> fileName <> "-opt" <.> "ll"
        callProcess "opt" $ optFlag ["-S", llFile, "-o", optLlFile]
        return (optLlFile, optFlag)
    let asmFile = asmDir </> fileName <.> "s"
    callProcess "llc" $ optFlag ["-march=x86-64", optLlFile, "-o", asmFile]
    ldFlags <- readProcess "pkg-config" ["--libs", "--static", "bdw-gc"] ""
    callProcess "gcc" $ concatMap words (lines ldFlags) ++ optFlag [asmFile, "-o", outputFile opts]
  where
    withAssemblyDir Nothing k = withSystemTempDirectory "sixten" k
    withAssemblyDir (Just dir) k = do
      createDirectoryIfMissing True dir
      k dir
