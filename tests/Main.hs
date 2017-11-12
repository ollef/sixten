import Control.Applicative   (liftA)
import Control.Monad         (join, filterM)
import Data.List        (isInfixOf, isSuffixOf)
import Data.Proxy       (Proxy (..))
import System.Directory (doesDirectoryExist, listDirectory, doesFileExist)
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

extraFlags :: FilePath -> [FilePath] -> Maybe FilePath -> [String]
extraFlags dir input expected = input ++ (f dir) ++ (g expected)
  where
    f d
      | "type-error"   `isInfixOf` d = ["--expect-type-error"]
      | "syntax-error" `isInfixOf` d = ["--expect-syntax-error"]
      | "success"      `isInfixOf` d = []
      | otherwise                    = undefined
    g Nothing  = []
    g (Just e) = ["--expected", e]

testInput :: IO [(String, [String], Maybe String)]
testInput = do
  ds <- join . liftA (filterM doesDirectoryExist) $
    fmap (testRootDir </>) <$> listDirectory testRootDir
  liftA concat $ mapM getInfo ds
    where
      getInfo dir
        | "-multi" `isSuffixOf` dir = multi dir
        | otherwise = single dir
      single dir = findByExtension [".vix"] dir >>= mapM g
        where
          g v = let e = v ++ "-expected" in do
            b <- doesFileExist e
            return $ f (v, extraFlags dir [v] $ pick e b)
      multi dir = do
        vs <- groupByKey takeDirectory <$> findByExtension [".vix"] dir
        mapM g vs
          where
            g (d, v) = let e = d </> "Main.hs-expected" in do
              b <- doesFileExist e
              return $ f (d, extraFlags d v $ pick e b)
      f (path, x) = (testName path, x, Nothing)
      pick e b = if b then Just e else Nothing

mkTestGrp :: Args -> [(TestName, [String], Maybe FilePath)] -> TestTree
mkTestGrp (A a) = testGroup "End to end tests" . fmap mkTest
  where
    mkTest (name, xs, stdin) =
      testProgram name "sixten" ("test" : (words a ++ xs)) stdin
