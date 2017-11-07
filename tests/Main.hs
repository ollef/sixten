import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy as LBS
import System.FilePath (FilePath, (</>))
import Test.Tasty (TestTree, testGroup, defaultMain)
import qualified Test.Tasty.Golden as Golden
import System.Process (readProcess)

main :: IO ()
main = do
  vixPaths <- Golden.findByExtension [".vix"] $ testRootDir </> testDir Success
  defaultMain $ tests vixPaths

data SuccessTest = Success | SuccessMulti

tests :: [FilePath] -> TestTree
tests vix = testGroup "Tests" [goldenTests vix]

testRootDir :: FilePath
testRootDir = "tests"

testDir :: SuccessTest -> FilePath
testDir Success = "success"
testDir SuccessMulti = "success-multi"

callSixten :: [String] -> String -> IO LBS.ByteString
callSixten a b = LBS.fromStrict . BS.pack <$> readProcess "sixten" a b

goldenTests :: [FilePath] -> TestTree
goldenTests vixPaths = testGroup "End to end tests"
  [ testGroup "Success tests" $ mkTest <$> vixPaths
  ]
  where
    mkTest v = Golden.goldenVsString (testName v) (goldenFilePath v) (output v)
    testDirStrLen = (length testRootDir + 1)
    testName = drop testDirStrLen
    goldenFilePath = flip (++) "-expected"
    output v = callSixten ["run", v] ""
