{-# LANGUAGE OverloadedStrings #-}
module Command.Compile where

import Control.Monad
import Data.Maybe
import GHC.IO.Handle
import Options.Applicative
import System.Directory
import System.FilePath
import System.IO
import System.IO.Temp
import System.Process

import qualified Backend.Target as Target
import Backend.Target(Target)
import qualified Processor

data Options = Options
  { inputFile :: FilePath
  , maybeOutputFile :: Maybe FilePath
  , target :: Maybe String
  , optimisation :: Maybe String
  , assemblyDir :: Maybe FilePath
  , verbosity :: Int
  , logFile :: Maybe FilePath
  } deriving (Show)

optionsParserInfo :: ParserInfo Options
optionsParserInfo = info (helper <*> optionsParser)
  $ fullDesc
  <> progDesc "Compile a Sixten program"
  <> header "sixten compile"

optionsParser :: Parser Options
optionsParser = Options
  <$> strArgument
    (metavar "FILE"
    <> help "Input source FILE"
    <> action "file"
    )
  <*> optional (strOption
    $ long "output"
    <> short 'o'
    <> metavar "FILE"
    <> help "Write output to FILE"
    <> action "file"
    )
  <*> optional (strOption
    $ long "target"
    <> short 't'
    <> metavar "TARGET"
    <> help "Compile for CPU architecture TARGET"
    <> completeWith Target.architectures
    )
  <*> optional (strOption
    $ long "optimise"
    <> short 'O'
    <> metavar "LEVEL"
    <> help "Set the optimisation level to LEVEL"
    <> completeWith ["0", "1", "2", "3"]
    )
  <*> optional (strOption
    $ long "save-assembly"
    <> short 'S'
    <> metavar "DIR"
    <> help "Save intermediate assembly files to DIR"
    <> action "directory"
    )
  <*> option auto
    (long "verbose"
    <> short 'v'
    <> metavar "LEVEL"
    <> help "Set the verbosity level to LEVEL"
    <> value 0
    <> completeWith ["0", "10", "20", "30", "40"]
    )
  <*> optional (strOption
    $ long "log-file"
    <> metavar "FILE"
    <> help "Write logs to FILE instead of standard output"
    <> action "file"
    )

compile
  :: Options
  -> (Processor.Error -> IO a)
  -> (FilePath -> IO a)
  -> IO a
compile opts onError onSuccess = case maybe (Right Target.defaultTarget) Target.findTarget $ target opts of
  Left err -> onError $ Processor.CommandLineError err
  Right tgt ->
    withAssemblyDir (assemblyDir opts) $ \asmDir ->
    withOutputFile (maybeOutputFile opts) $ \outputFile ->
    withLogHandle (logFile opts) $ \logHandle -> do
      let llFile = asmDir </> fileName <.> "ll"
          linkedLlFileName = asmDir </> fileName <.> "linked" <.> "ll"
          cFile = asmDir </> fileName <.> "c"
      procResult <- Processor.processFile Processor.ProcessFileArgs
        { Processor.procFile = inputFile opts
        , Processor.procLlOutput = llFile
        , Processor.procCOutput = cFile
        , Processor.procTarget = tgt
        , Processor.procLogHandle = logHandle
        , Processor.procVerbosity = verbosity opts
        }
      case procResult of
        Processor.Error err -> onError err
        Processor.Success cFiles -> do
          cLlFiles <- forM cFiles $ clangCompile opts tgt
          linkedLlFile <- llvmLink (llFile : cLlFiles) linkedLlFileName
          optLlFile <- llvmOptimise opts linkedLlFile
          objFile <- llvmCompile opts tgt optLlFile
          assemble opts objFile outputFile
          onSuccess outputFile
  where
    (inputDir, inputFileName) = splitFileName $ inputFile opts
    fileName = dropExtension inputFileName

    withAssemblyDir Nothing k = withSystemTempDirectory "sixten" k
    withAssemblyDir (Just dir) k = do
      createDirectoryIfMissing True dir
      k dir
    withOutputFile Nothing k
      = withTempFile inputDir fileName $ \outputFile outputFileHandle -> do
        hClose outputFileHandle
        k outputFile
    withOutputFile (Just o) k = k o
    withLogHandle Nothing k = k stdout
    withLogHandle (Just file) k = withFile file WriteMode k

optimisationFlags :: Options -> [String]
optimisationFlags opts = case optimisation opts of
  Nothing -> []
  Just optLevel -> ["-O" <> optLevel]

llvmOptimise :: Options -> FilePath -> IO FilePath
llvmOptimise opts llFile
  | isNothing $ optimisation opts = return llFile
  | otherwise = do
    let optLlFile = replaceExtension llFile "opt.ll"
    callProcess "opt" $ optimisationFlags opts ++ ["-S", llFile, "-o", optLlFile]
    return optLlFile

clangCompile :: Options -> Target -> FilePath -> IO FilePath
clangCompile opts tgt cFile = do
  let outputFile = cFile <> ".ll"
  callProcess "clang" $ optimisationFlags opts ++
    [ "-march=" <> Target.architecture tgt
    , "-fvisibility=internal"
    , "-S"
    , "-emit-llvm"
    , cFile
    , "-o", outputFile
    ]
  return outputFile

llvmLink :: [FilePath] -> FilePath -> IO FilePath
llvmLink [file] _outputFile = return file
llvmLink files outputFile = do
  callProcess "llvm-link" $ ["-o=" <> outputFile, "-S"] ++ files
  return outputFile

llvmCompile :: Options -> Target -> FilePath -> IO FilePath
llvmCompile opts tgt llFile = do
  let flags ft o
        = optimisationFlags opts ++
        [ "-filetype=" <> ft
        , "-march=" <> Target.architecture tgt
        , llFile
        , "-o", o
        ]
      asmFile = replaceExtension llFile "s"
      objFile = replaceExtension llFile "o"
  when (isJust $ assemblyDir opts) $
    callProcess "llc" $ flags "asm" asmFile
  callProcess "llc" $ flags "obj" objFile
  return objFile

assemble :: Options -> FilePath -> FilePath -> IO ()
assemble opts objFile outputFile = do
  ldFlags <- readProcess "pkg-config" ["--libs", "--static", "bdw-gc"] ""
  callProcess "clang"
    $ concatMap words (lines ldFlags)
    ++ optimisationFlags opts
    ++ [objFile, "-o", outputFile]

command :: ParserInfo (IO ())
command = go <$> optionsParserInfo
  where
    go opts = compile opts Processor.printError (const $ return ())
