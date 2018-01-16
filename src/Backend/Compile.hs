{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Backend.Compile where

import Control.Exception
import Control.Monad
import Data.Char
import Data.Foldable
import Data.List (dropWhile, dropWhileEnd)
import Data.Maybe
import Data.Monoid
import Data.Version
import System.FilePath
import System.Process
import Text.Printf

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

minLlvmVersion :: Int
minLlvmVersion = 4

maxLlvmVersion :: Int
maxLlvmVersion = 5

-- See http://blog.llvm.org/2016/12/llvms-new-versioning-scheme.html
-- Tl;dr: minor versions are fixed to 0, so only different major versions need
-- to be supported.
supportedLlvmVersions :: [Version]
supportedLlvmVersions = makeVersion . (: [minorVersion]) <$> supportedMajorVersions
  where minorVersion = 0
        supportedMajorVersions = [maxLlvmVersion, maxLlvmVersion - 1 .. minLlvmVersion]

-- | llvm-config is not available in current LLVM distribution for windows, so we
-- need use @clang -print-prog-name=clang@ to get the full path of @clang@.
--
-- We simply assume that @clang.exe@ already exists in @%PATH%@.
--
clangBinPath :: String -> IO FilePath
clangBinPath command = trim <$> checkClangExists trySuffixes
  where trySuffixes = "" : fmap (('-' :) . showVersion) supportedLlvmVersions
        checkClangExists (suffix : xs) =
          handle (\(_ :: IOException) -> checkClangExists xs)
          $ readProcess (command ++ suffix) ["-print-prog-name=" ++ command ++ suffix] ""
        checkClangExists [] = error (
          (printf ("Couldn't find clang. Currently supported versions are " <>
                   "%d <= v <= %d.") minLlvmVersion maxLlvmVersion) :: String)
        trim = dropWhile isSpace . dropWhileEnd isSpace

llvmBinPath :: IO FilePath
llvmBinPath = checkLlvmExists trySuffixes
  where trySuffixes = "" : fmap (('-' :) . showVersion) supportedLlvmVersions
        checkLlvmExists :: [String] -> IO String
        checkLlvmExists (suffix : xs) =
          handle (\(_ :: IOException) -> checkLlvmExists xs)
          $ readProcess ("llvm-config" ++ suffix) ["--bindir"] ""
        checkLlvmExists [] = error (
          (printf ("Couldn't find llvm-config. Currently supported versions are " <>
                   "%d <= v <= %d.\n You can specify its path using the " <>
                   "--llvm-config flag.") minLlvmVersion maxLlvmVersion) :: String)

compile :: Options -> Arguments -> IO ()
compile opts args = do
#ifndef mingw32_HOST_OS
  binPath <- takeWhile (not . isSpace) <$> case Options.llvmConfig opts of
    Nothing -> llvmBinPath
    Just configBin -> do
      majorVersion <- read . takeWhile (not . (== '.'))
        <$> readProcess configBin ["--version"] ""
      if minLlvmVersion <= majorVersion && majorVersion <= maxLlvmVersion then
        readProcess configBin ["--bindir"] ""
      else error (
          (printf ("LLVM version out of range. Currently supported versions are " <>
                   "%d <= v <= %d.\n") minLlvmVersion maxLlvmVersion) :: String)
  let opt = binPath </> "opt"
  let clang = binPath </> "clang"
  let linker = binPath </> "llvm-link"
  let compiler = binPath </> "llc"
  cLlFiles <- forM (cFiles args) $ compileC clang opts $ target args
  linkedLlFile <- linkLlvm linker (llFiles args ++ toList cLlFiles)
    $ linkedLlFileName args
  optLlFile <- optimiseLlvm opt opts linkedLlFile
  objFile <- compileLlvm compiler opts (target args) optLlFile
  assemble clang opts [objFile] $ outputFile args
#else
  -- In LLVM distribution for windows, @opt@, @llvm-link@ and @llc@ are not
  -- available. We use @clang@ to link llvm files directly.
  -- We enable @-fLTO@ in @assemble@ to perform link time optimizations.
  clang <- clangBinPath "clang"
  cLlFiles <- forM (cFiles args) $ compileC clang opts $ target args
  assemble clang opts (llFiles args ++ toList cLlFiles) $ outputFile args
#endif

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
#ifndef mingw32_HOST_OS
    , "-fPIC"
#endif
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

assemble :: Binary -> Options -> [FilePath] -> FilePath -> IO ()
assemble clang opts objFiles outFile = do
#ifndef mingw32_HOST_OS
  ldFlags <- readProcess "pkg-config" ["--libs", "--static", "bdw-gc"] ""
#else
  -- Currently the bdwgc can only output library linking with dynamic MSVCRT.
  -- however clang will automatically pass static MSVCRT to linker.
  let ldFlags = "-lgc-lib -fuse-ld=lld-link -Xlinker -nodefaultlib:libcmt -Xlinker -defaultlib:msvcrt.lib"
#endif
  callProcess clang
    $ concatMap words (lines ldFlags)
    ++ optimisationFlags opts
    ++ ["-flto"]
    ++ objFiles ++ ["-o", outFile]
