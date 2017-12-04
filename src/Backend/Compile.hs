{-# LANGUAGE ScopedTypeVariables #-}

module Backend.Compile where

import Control.Exception
import Control.Monad
import Data.Foldable
import Data.Maybe
import Data.Monoid
import Data.Version
import System.FilePath
import System.Process

import Backend.Target(Target)
import qualified Backend.Target as Target
import Command.Compile.Options(Options)
import qualified Command.Compile.Options as Options

data Arguments = Arguments
  { cFiles :: [FilePath]
  , llFiles :: [FilePath]
  , linkedLlFileName :: !FilePath
  , target :: !Target
  , outputFile :: !FilePath
  }

supportedLlvmVersions :: [Version]
supportedLlvmVersions = makeVersion <$> [[5, 0], [4, 0]]

llvmBinSuffix :: IO String
llvmBinSuffix = checkLlvmExists trySuffixes
  where trySuffixes = "" : fmap (('-' :) . showVersion) supportedLlvmVersions
        checkLlvmExists :: [String] -> IO String
        checkLlvmExists (suffix : xs) =
          handle (\(_ :: IOException) -> checkLlvmExists xs) $ do
          _ <- readProcess ("llvm-config" ++ suffix) ["--version"] ""
          return suffix
        checkLlvmExists [] =
          error "Couldn't find LLVM binaries for supported versions.\n\
                \Try using the --llvm-config flag."

compile :: Options -> Arguments -> IO ()
compile opts args = do
  suffix <- llvmBinSuffix
  let opt = "opt" ++ suffix
  let clang = "clang" ++ suffix
  let linker = "llvm-link" ++ suffix
  let compiler = "llc" ++ suffix
  cLlFiles <- forM (cFiles args) $ compileC clang opts $ target args
  linkedLlFile <- linkLlvm linker (llFiles args ++ toList cLlFiles)
    $ linkedLlFileName args
  optLlFile <- optimiseLlvm opt opts linkedLlFile
  objFile <- compileLlvm compiler opts (target args) optLlFile
  assemble clang opts objFile $ outputFile args

optimisationFlags :: Options -> [String]
optimisationFlags opts = case Options.optimisation opts of
  Nothing -> []
  Just optLevel -> ["-O" <> optLevel]

type Binary = FilePath

optimiseLlvm :: Binary -> Options -> FilePath -> IO FilePath
optimiseLlvm opt opts file
  | isNothing $ Options.optimisation opts = return file
  | otherwise = do
    let optLlFile = replaceExtension file "opt.ll"
    callProcess opt $ optimisationFlags opts ++
      [ "-S", file
      , "-o", optLlFile
      ]
    return optLlFile

compileC :: Binary -> Options -> Target -> FilePath -> IO FilePath
compileC clang opts tgt cFile = do
  let output = cFile <> ".ll"
  callProcess clang $ optimisationFlags opts ++
    [ "-march=" <> Target.architecture tgt
    , "-fvisibility=internal"
    , "-fPIC"
    , "-S"
    , "-emit-llvm"
    , cFile
    , "-o", output
    ]
  return output

linkLlvm :: Binary -> [FilePath] -> FilePath -> IO FilePath
linkLlvm _ [file] _outFile = return file
linkLlvm linker files outFile = do
  callProcess linker $ ["-o=" <> outFile, "-S"] ++ files
  return outFile

compileLlvm :: Binary -> Options -> Target -> FilePath -> IO FilePath
compileLlvm compiler opts tgt llFile = do
  let flags ft o
        = optimisationFlags opts ++
        [ "-filetype=" <> ft
        , "-march=" <> Target.architecture tgt
        , "-relocation-model=pic"
        , llFile
        , "-o", o
        ]
      asmFile = replaceExtension llFile "s"
      objFile = replaceExtension llFile "o"
  when (isJust $ Options.assemblyDir opts) $
    callProcess compiler $ flags "asm" asmFile
  callProcess compiler $ flags "obj" objFile
  return objFile

assemble :: Binary -> Options -> FilePath -> FilePath -> IO ()
assemble clang opts objFile outFile = do
  ldFlags <- readProcess "pkg-config" ["--libs", "--static", "bdw-gc"] ""
  callProcess clang
    $ concatMap words (lines ldFlags)
    ++ optimisationFlags opts
    ++ [objFile, "-o", outFile]
