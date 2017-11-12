import Data.Proxy       (Proxy (..))
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

groupByKey :: Ord b => (a -> b) -> [a] -> [(b, [a])]
groupByKey _  [] = []
groupByKey f (x : xs) = (kx, x : xlike) : groupByKey f rest
  where kx = f x
        (xlike, rest) = span ((==) kx . f) xs

testInput :: IO [(String, [String], Maybe String)]
testInput = do
  fmap concat $ sequence
    [ single "success" []
    , single "type-error" ["--expect-type-error"]
    , single "syntax-error" ["--expect-syntax-error"]
    , multi "success-multi" []
    , multi "type-error-multi" ["--expect-type-error"]
    ]
    where
      single dir flags = getVix dir >>= mapM g
        where
          g v = let e = v ++ "-expected" in do
            b <- doesFileExist e
            return $ f (v, flags ++ (v : pick e b))
      multi dir flags = do
        vs <- groupByKey takeDirectory <$> getVix dir
        mapM g vs
          where
            g (d, v) = let e = d </> "Main.hs-expected" in do
              b <- doesFileExist e
              return $ f (d, flags ++ v ++ pick e b)
      getVix dir = findByExtension [".vix"] $ testRootDir </> dir
      f (path, x) = (testName path, x, Nothing)
      pick e b = if b then ["--expected", e] else []

mkTestGrp :: Args -> [(TestName, [String], Maybe FilePath)] -> TestTree
mkTestGrp (A a) = testGroup "End to end tests" . fmap mkTest
  where
    mkTest (name, xs, stdin) =
      testProgram name "sixten" ("test" : (words a ++ xs)) stdin
