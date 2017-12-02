import Data.List
import Data.Proxy       (Proxy (..))
import Data.Traversable
import System.Directory (doesFileExist)
import System.FilePath  (takeDirectory, FilePath, (</>))
import Test.Tasty
import Test.Tasty.Golden  (findByExtension)
import Test.Tasty.Options (IsOption (..), OptionDescription (Option))
import Test.Tasty.Program (testProgram)


main :: IO ()
main = do
  input <- testInput
  defaultMainWithIngredients ings . askOption $ \args -> mkTestGrp args input
    where
      ings = includingOptions [Option (Proxy :: Proxy Args)] :
        defaultIngredients

newtype Args = A String

instance IsOption Args where
  defaultValue = A ""
  parseValue = Just . A
  optionName = return "sixten-args"
  optionHelp = return "Arguments to supply to the sixten binary."

testRootDir :: FilePath
testRootDir = "tests"
testName :: FilePath -> FilePath
testName = drop (length testRootDir + 1)

groupByKey :: Eq b => (a -> b) -> [a] -> [(b, [a])]
groupByKey _  [] = []
groupByKey f (x : xs) = (kx, x : xlike) : groupByKey f rest
  where kx = f x
        (xlike, rest) = span ((==) kx . f) xs

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
      vixDirs <- groupByKey takeDirectory <$> findVixFiles dir
      forM vixDirs $ \(dir, files) -> do
        let expFile = dir </> "Main.hs-expected"
        expExists <- doesFileExist expFile
        return (testName dir, flags ++ files ++ expectedFlag expFile expExists)

    findVixFiles dir = sort <$> findByExtension [".vix"] (testRootDir </> dir)

    expectedFlag file exists = if exists then ["--expected", file] else []

mkTestGrp :: Args -> [(TestName, [String])] -> TestTree
mkTestGrp (A a) = testGroup "End to end tests" . fmap mkTest
  where
    mkTest (name, xs) =
      testProgram name "sixten" ("test" : (words a ++ xs)) Nothing
