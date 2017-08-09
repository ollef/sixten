module Backend.Compile where

import Control.Monad
import Data.Foldable
import Data.Maybe
import Data.Monoid
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

compile :: Options -> Arguments -> IO ()
compile opts args = do
  cLlFiles <- forM (cFiles args) $ compileC opts $ target args
  linkedLlFile <- linkLlvm (llFiles args ++ toList cLlFiles) $ linkedLlFileName args
  optLlFile <- optimiseLlvm opts linkedLlFile
  objFile <- compileLlvm opts (target args) optLlFile
  assemble opts objFile $ outputFile args

optimisationFlags :: Options -> [String]
optimisationFlags opts = case Options.optimisation opts of
  Nothing -> []
  Just optLevel -> ["-O" <> optLevel]

optimiseLlvm :: Options -> FilePath -> IO FilePath
optimiseLlvm opts file
  | isNothing $ Options.optimisation opts = return file
  | otherwise = do
    let optLlFile = replaceExtension file "opt.ll"
    callProcess "opt" $ optimisationFlags opts ++
      [ "-S", file
      , "-o", optLlFile
      ]
    return optLlFile

compileC :: Options -> Target -> FilePath -> IO FilePath
compileC opts tgt cFile = do
  let output = cFile <> ".ll"
  callProcess "clang" $ optimisationFlags opts ++
    [ "-march=" <> Target.architecture tgt
    , "-fvisibility=internal"
    , "-fPIC"
    , "-S"
    , "-emit-llvm"
    , cFile
    , "-o", output
    ]
  return output

linkLlvm :: [FilePath] -> FilePath -> IO FilePath
linkLlvm [file] _outFile = return file
linkLlvm files outFile = do
  callProcess "llvm-link" $ ["-o=" <> outFile, "-S"] ++ files
  return outFile

compileLlvm :: Options -> Target -> FilePath -> IO FilePath
compileLlvm opts tgt llFile = do
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
    callProcess "llc" $ flags "asm" asmFile
  callProcess "llc" $ flags "obj" objFile
  return objFile

assemble :: Options -> FilePath -> FilePath -> IO ()
assemble opts objFile outFile = do
  ldFlags <- readProcess "pkg-config" ["--libs", "--static", "bdw-gc"] ""
  callProcess "clang"
    $ concatMap words (lines ldFlags)
    ++ optimisationFlags opts
    ++ [objFile, "-o", outFile]
