module Main where

import Prelude(String)
import Protolude

import qualified Data.HashSet as HashSet
import Data.List
import Data.Proxy(Proxy (..))
import System.Directory(doesFileExist)
import System.FilePath(takeDirectory, FilePath, (</>))
import Test.Tasty
import Test.Tasty.Golden(findByExtension)
import Test.Tasty.Options as Tasty
import Test.Tasty.Program(testProgram)

main :: IO ()
main = do
  input <- testInput
  defaultMainWithIngredients ings . askOption $ \args -> mkTestGrp args input
    where
      ings = includingOptions [Tasty.Option (Proxy :: Proxy Args)] :
        defaultIngredients

newtype Args = A String

instance Tasty.IsOption Args where
  defaultValue = A ""
  parseValue = Just . A
  optionName = return "sixten-args"
  optionHelp = return "Arguments to supply to the sixten binary."

testRootDir :: FilePath
testRootDir = "tests"

testName :: FilePath -> FilePath
testName = drop (length testRootDir + 1)

testInput :: IO [(String, [String])]
testInput = concat <$> sequence
  [ single "success" []
  , single "type-error" ["--expect-type-error"]
  , single "syntax-error" ["--expect-syntax-error"]
  , multi "success-multi" []
  , multi "type-error-multi" ["--expect-type-error"]
  ]
  where
    single dir flags = do
      vixFiles <- findVixFiles dir
      forM vixFiles $ \file -> do
        let expFile = file ++ "-expected"
        expExists <- doesFileExist expFile
        return (testName file, flags ++ file : expectedFlag expFile expExists)

    multi dir flags = do
      vixFiles <- findVixFiles dir
      let vixDirs = HashSet.fromList $ takeDirectory <$> vixFiles
      forM (toList vixDirs) $ \subDir -> do
        let expFile = subDir </> "Main.vix-expected"
        expExists <- doesFileExist expFile
        return (testName subDir, flags ++ [subDir] ++ expectedFlag expFile expExists)

    findVixFiles dir = sort <$> findByExtension [".vix"] (testRootDir </> dir)

    expectedFlag file exists = if exists then ["--expected", file] else []

mkTestGrp :: Args -> [(TestName, [String])] -> TestTree
mkTestGrp (A a) = testGroup "End to end tests" . fmap mkTest
  where
    mkTest (name, xs) =
      testProgram name "sixten" ("test" : (words a ++ xs)) Nothing
