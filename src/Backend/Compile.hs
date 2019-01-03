{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Backend.Compile where

import Protolude hiding (moduleName, (<.>))

import Data.Char
import Data.List(dropWhile, dropWhileEnd)
import Data.String
import qualified Data.Text.IO as Text
import Data.Version
import System.Directory
import System.FilePath
import System.IO.Temp
import System.Process
import Text.Printf

import qualified Backend.Generate as Generate
import qualified Backend.Generate.Submodule as Generate
import Backend.Target(Target)
import qualified Backend.Target as Target
import qualified Command.Compile.Options as Compile
import Syntax.Extern
import Syntax.ModuleHeader
import Syntax.QName
import Util

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
maxLlvmVersion = 7

-- See http://blog.llvm.org/2016/12/llvms-new-versioning-scheme.html
-- Tl;dr: minor versions are fixed to 0, so only different major versions need
-- to be supported.
supportedLlvmVersions :: [Version]
supportedLlvmVersions = makeVersion . (: [minorVersion]) <$> supportedMajorVersions
  where
    minorVersion = 0
    supportedMajorVersions = [maxLlvmVersion, maxLlvmVersion - 1 .. minLlvmVersion]

-- | llvm-config is not available in current LLVM distribution for windows, so we
-- need use @clang -print-prog-name=clang@ to get the full path of @clang@.
--
-- We simply assume that @clang.exe@ already exists in @%PATH%@.
--
clangBinPath :: IO FilePath
clangBinPath = trim <$> checkClangExists
  where
    checkClangExists =
      handle (\(_ :: IOException) -> panic "Couldn't find clang.")
      $ readProcess "clang" ["-print-prog-name=clang"] ""
    trim = dropWhile isSpace . dropWhileEnd isSpace

llvmBinPath :: IO FilePath
llvmBinPath = checkLlvmExists candidates
  where
    suffixes
      = ""
      -- The naming scheme on e.g. Ubuntu:
      : fmap (("-" <>) . showVersion) supportedLlvmVersions
    prefixes =
      [ ""
      -- The installation path of Brew on Mac:
      , "/usr/local/opt/llvm/bin/"
      ]
    candidates
      = ["llvm-config" <> suffix | suffix <- suffixes]
      ++ [prefix <> "llvm-config" | prefix <- prefixes]

    checkLlvmExists :: [String] -> IO FilePath
    checkLlvmExists (path : xs) =
      handle (\(_ :: IOException) -> checkLlvmExists xs)
      $ readProcess path ["--bindir"] ""
    checkLlvmExists [] = panic
      "Couldn't find llvm-config. You can specify its path using the --llvm-config flag."

compileFiles :: Compile.Options -> Arguments -> IO ()
compileFiles opts args = do
#ifndef mingw32_HOST_OS
  binPath <- takeWhile (not . isSpace) <$> case Compile.llvmConfig opts of
    Nothing -> llvmBinPath
    Just configBin -> do
      maybeMajorVersion <- readMaybe . takeWhile (/= '.')
        <$> readProcess configBin ["--version"] ""
      case maybeMajorVersion of
        Nothing -> printf
          "Warning: Couldn't determine LLVM version. Currently supported versions are %d <= v <= %d.\n"
          minLlvmVersion
          maxLlvmVersion
        Just majorVersion ->
          when (majorVersion < minLlvmVersion || majorVersion > maxLlvmVersion) $
            printf
              "Warning: LLVM version out of range. Currently supported versions are %d <= v <= %d.\n"
              minLlvmVersion
              maxLlvmVersion
      readProcess configBin ["--bindir"] ""
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
  clang <- clangBinPath
  cLlFiles <- forM (cFiles args) $ compileC clang opts $ target args
  assemble clang opts (llFiles args ++ toList cLlFiles) $ outputFile args
#endif

optimisationFlags :: Compile.Options -> [String]
optimisationFlags opts = case Compile.optimisation opts of
  Nothing -> []
  Just optLevel -> ["-O" <> optLevel]

type Binary = FilePath

optimiseLlvm :: Binary -> Compile.Options -> FilePath -> IO FilePath
optimiseLlvm opt opts file
  | isNothing $ Compile.optimisation opts = return file
  | otherwise = do
    let optLlFile = replaceExtension file "opt.ll"
    callProcess opt $ optimisationFlags opts ++
      [ "-S", file
      , "-o", optLlFile
      ]
    return optLlFile

compileC :: Binary -> Compile.Options -> Target -> FilePath -> IO FilePath
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

compileLlvm :: Binary -> Compile.Options -> Target -> FilePath -> IO FilePath
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
  when (isJust $ Compile.assemblyDir opts) $
    callProcess compiler $ flags "asm" asmFile
  callProcess compiler $ flags "obj" objFile
  return objFile

assemble :: Binary -> Compile.Options -> [FilePath] -> FilePath -> IO ()
assemble clang opts objFiles outFile = do
  let extraLibDirFlag = ["-L" ++ dir | dir <- Compile.extraLibDir opts]
#ifndef mingw32_HOST_OS
  ldFlags <- readProcess "pkg-config" ["--libs", "--static", "bdw-gc"] ""
#else
  -- Currently the bdwgc can only output library linking with dynamic MSVCRT.
  -- however clang will automatically pass static MSVCRT to linker.
  let ldFlags = "-lgc-lib -fuse-ld=lld-link -Xlinker -nodefaultlib:libcmt -Xlinker -defaultlib:msvcrt.lib"
#endif
  callProcess clang
    $ concatMap words (extraLibDirFlag ++ lines ldFlags)
    ++ optimisationFlags opts
    ++ objFiles ++ ["-o", outFile]

compileModules
  :: FilePath
  -> Target
  -> Compile.Options
  -> [(ModuleHeader, [Generate.Submodule])]
  -> IO ()
compileModules outputFile_ target_ opts modules =
  withAssemblyDir (Compile.assemblyDir opts) $ \asmDir -> do
    (externFiles, llFiles_)
      <- fmap mconcat $ forM modules $ \(moduleHeader, subModules) -> do
        let fileBase = asmDir </> fromModuleName (moduleName moduleHeader)
            llName = fileBase <> ".ll"
            cName = fileBase <> ".c"
        externs <- writeModule moduleHeader subModules llName [(C, cName)]
        return (externs, [llName])
    let linkedLlFileName_ = asmDir </> "main" <.> "linked" <.> "ll"
    compileFiles opts Arguments
      { cFiles = [cFile | (C, cFile) <- externFiles]
      , llFiles = llFiles_
      , linkedLlFileName = linkedLlFileName_
      , target = target_
      , outputFile = outputFile_
      }
  where
    withAssemblyDir Nothing k = withSystemTempDirectory "sixten" k
    withAssemblyDir (Just dir) k = do
      createDirectoryIfMissing True dir
      k dir

writeModule
  :: ModuleHeader
  -> [Generate.Submodule]
  -> FilePath
  -> [(Language, FilePath)]
  -> IO [(Language, FilePath)]
writeModule moduleHeader subModules llOutputFile externOutputFiles = do
  Util.withFile llOutputFile WriteMode $
    Generate.writeLlvmModule
      (moduleName moduleHeader)
      (moduleImports moduleHeader)
      subModules
  fmap catMaybes $
    forM externOutputFiles $ \(lang, outFile) ->
      case fmap snd $ filter ((== lang) . fst) $ concatMap Generate.externs subModules of
        [] -> return Nothing
        externCode -> Util.withFile outFile WriteMode $ \h -> do
          -- TODO this is C specific
          Text.hPutStrLn h "#include <inttypes.h>"
          Text.hPutStrLn h "#include <stdint.h>"
          Text.hPutStrLn h "#include <stdio.h>"
          Text.hPutStrLn h "#include <stdlib.h>"
          Text.hPutStrLn h "#include <string.h>"
          Text.hPutStrLn h "#ifdef _WIN32"
          Text.hPutStrLn h "#include <io.h>"
          Text.hPutStrLn h "#else"
          Text.hPutStrLn h "#include <unistd.h>"
          Text.hPutStrLn h "#endif"
          forM_ externCode $ \code -> do
            Text.hPutStrLn h ""
            Text.hPutStrLn h code
          return $ Just (lang, outFile)
