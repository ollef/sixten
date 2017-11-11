import Control.Applicative (liftA)
import Data.ByteString.Char8 (pack)
import Data.ByteString.Lazy  (ByteString, fromStrict)
import Data.Proxy       (Proxy (..))
import System.FilePath  (takeDirectory, FilePath, (</>))
import System.Process   (readProcess)
import Test.Tasty
import Test.Tasty.Golden  (findByExtension)
import Test.Tasty.Options (IsOption (..), OptionDescription (Option))
import Test.Tasty.Program (testProgram)


main :: IO ()
main = do
  vix <- liftA concat . sequence $ getInput <$>
    [ TI {arity = Single [], expect = Success}
    , TI {arity = Single [], expect = SyntaxError}
    , TI {arity = Single [], expect = TypeError}
    , TI {arity = Multi ([], []), expect = Success}
    , TI {arity = Multi ([], []), expect = TypeError}
    ]
  defaultMainWithIngredients ings . askOption $ \args -> tests (args) vix
    where
      ings = includingOptions [Option (Proxy :: Proxy Args)] :
        defaultIngredients

newtype Args = A String

instance IsOption Args where
  defaultValue = A ""
  parseValue = Just . A
  optionName = return "sixten-args"
  optionHelp = return "Arguments to supply to the sixten binary."

tests :: Args -> [TestInput] -> TestTree
tests a vix = testGroup "Tests" [endToEndTests a vix]

testRootDir :: FilePath
testRootDir = "tests"

data InputArity = Single FilePath | Multi (FilePath, [FilePath])

data InputExpect = Success | SyntaxError | TypeError

data TestInput = TI { arity  :: InputArity
                    , expect :: InputExpect
                    }

findVixFiles :: TestInput -> IO [FilePath]
findVixFiles = findByExtension [".vix"] . testDir
  where
    testDir z = testRootDir </> (g z ++ h z)
    g TI {expect = Success}     = "success"
    g TI {expect = SyntaxError} = "syntax-error"
    g TI {expect = TypeError}   = "type-error"
    h TI {arity  = Single _} = ""
    h TI {arity  = Multi _}  = "-multi"

groupByKey :: Ord b => (a -> b) -> [a] -> [(b, [a])]
groupByKey _  [] = []
groupByKey f (x : xs) = (kx, x : xlike) : groupByKey f rest
  where kx = f x
        (xlike, rest) = span ((==) kx . f) xs

getInput :: TestInput -> IO [TestInput]
getInput t@(TI {arity = Single _}) = do
  v <- findVixFiles t
  return $ fmap (\x -> TI (Single x) (expect t)) v
getInput t@(TI {arity = Multi _}) = do
  v <- findVixFiles t
  return . fmap (\x -> TI (Multi x) (expect t)) $ groupByKey takeDirectory v

callSixten :: [String] -> String -> IO ByteString
callSixten a b = fromStrict . pack <$> readProcess "sixten" a b

endToEndTests :: Args -> [TestInput] -> TestTree
endToEndTests (A a) vix = testGroup "End to end tests" $ mkTest <$> vix
  where
    mkTest t = testProgram (testName t) "sixten" ("test" : args t) Nothing
    dropTestDirPrefix = drop (length testRootDir + 1)
    testName TI {arity = Single v}     = dropTestDirPrefix v
    testName TI {arity = Multi (d, _)} = dropTestDirPrefix d
    args t = words a ++ flags t ++ files t ++ expected t
    flags TI {expect = SyntaxError} = ["--expect-syntax-error"]
    flags TI {expect = TypeError}   = ["--expect-type-error"]
    flags _                         = []
    files TI {arity = Single v}     = [v]
    files TI {arity = Multi (_, v)} = v
    expected TI {expect = Success, arity = Single v} =
      ["--expected", v ++ "-expected"]
    expected TI {expect = Success, arity = Multi (d, _)} =
      ["--expected", d </> "Main.vix-expected"]
    expected _ = []
