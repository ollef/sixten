{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad.Except
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import Data.Monoid
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Data.Vector as V
import Data.Void
import System.Environment

import Builtin
import ClosureConvert
import Erase
import qualified Generate
import Infer
import qualified LLVM
import Meta
import TCM
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete as Concrete
import qualified Syntax.Lambda as Lambda
import qualified Syntax.Lifted as Lifted
import qualified Syntax.Parse as Parse
import qualified Syntax.Resolve as Resolve
import Restrict
import Util

processGroup
  :: [(Name, Definition Concrete.Expr Name, Concrete.Expr Name)]
  -> TCM s [(Name, LLVM.B)]
processGroup
  = exposeGroup
  >=> typeCheckGroup
  >=> addGroupToContext
  >=> eraseGroup
  >=> restrictGroup
  >=> liftGroup "-restrict"
  >=> addGroupAritiesToContext
  >=> closureConvertGroup
  >=> liftGroup "-convert"
  >=> generateGroup

exposeGroup
  :: [(Name, Definition Concrete.Expr Name, Concrete.Expr Name)]
  -> TCM s [(Name, Definition Concrete.Expr (Var Int v), Scope Int Concrete.Expr v)]
exposeGroup defs = return
  [ ( n
    , s >>>= unvar (pure . B) Concrete.Global
    , t >>>= Concrete.Global
    )
  | ((s, t), (n, _, _)) <- zip (zip abstractedScopes abstractedTypes) defs]
  where
    abstractedScopes = recursiveAbstractDefs [(n, d) | (n, d, _) <- defs]
    abstractedTypes = recursiveAbstract [(n, t) | (n, _, t) <- defs]

typeCheckGroup
  :: [(Name, Definition Concrete.Expr (Var Int (MetaVar Abstract.Expr s)), ScopeM Int Concrete.Expr s)]
  -> TCM s [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
typeCheckGroup defs = do
  checkedDefs <- checkRecursiveDefs $ V.fromList defs

  let vf :: a -> TCM s b
      vf _ = throwError "typeCheckGroup"
  checkedDefs' <- traverse (bitraverse (traverse $ traverse vf) (traverse vf)) checkedDefs
  let names = V.fromList [n | (n, _, _) <- defs]
      instDefs =
        [ ( names V.! i
          , instantiateDef (Abstract.Global . (names V.!)) d
          , instantiate (Abstract.Global . (names V.!)) t
          )
        | (i, (d, t)) <- zip [0..] $ V.toList checkedDefs'
        ]
  return instDefs

addGroupToContext
  :: [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> TCM s [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
addGroupToContext defs = do
  addContext $ HM.fromList $ (\(n, d, t) -> (n, (d, t))) <$> defs
  return defs

eraseGroup
  :: [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)] 
  -> TCM s [(Name, Definition Lambda.SExpr Void)]
eraseGroup defs = forM defs $ \(x, e, _) -> (,) x <$> eraseDef e

restrictGroup
  :: [(Name, Definition Lambda.SExpr Void)]
  -> TCM s [(Name, Lifted.LBody Void)]
restrictGroup defs = sequence
  [ do
      e' <- Restrict.restrictBody (vacuous e)
      e'' <- traverse (throwError . ("restrictGroup " ++) . show) e'
      return (x, e'')
  | (x, Definition e) <- defs
  ]

liftGroup
  :: Name
  -> [(Name, Lifted.LBody Void)]
  -> TCM s [(Name, Lifted.Body Void)]
liftGroup name defs = do
  let defs' = Restrict.liftProgram name $ fmap vacuous <$> defs
  traverse (traverse (traverse (throwError . ("liftGroup " ++) . show))) defs'

addGroupAritiesToContext
  :: [(Name, Lifted.Body Void)]
  -> TCM s [(Name, Lifted.Body Void)]
addGroupAritiesToContext defs = do
  forM_ defs $ \(x, b) -> addArity x $ case b of
    Lifted.FunctionBody (Lifted.Function _ xs _) -> V.length xs
    Lifted.ConstantBody _ -> 0
  return defs

closureConvertGroup
  :: [(Name, Lifted.Body Void)]
  -> TCM s [(Name, Lifted.LBody Void)]
closureConvertGroup defs = do
  defs' <- forM defs $ \(x, e) -> (,) x <$> ClosureConvert.convertBody (vacuous e)
  traverse (traverse (traverse (throwError . ("closureConvertGroup " ++) . show))) defs'

generateGroup
  :: [(Name, Lifted.Body Void)]
  -> TCM s [(LLVM.B, LLVM.B)]
generateGroup defs = do
  qcindex <- qconstructorIndex
  let defMap = HM.fromList defs
      env = Generate.GenEnv qcindex (`HM.lookup` defMap)
  return $ flip map defs $ \(x, e) ->
    second (fold . intersperse "\n")
      $ Generate.runGen env
      $ Generate.generateBody x $ vacuous e

processFile :: FilePath -> IO ()
processFile file = do
  parseResult <- Parse.parseFromFile Parse.program file
  let resolveResult = Resolve.program <$> parseResult
  case resolveResult of
    Nothing -> return ()
    Just (Left err) -> Text.putStrLn err
    Just (Right resolved) -> do
      let constrs = HS.fromList
                  $ programConstrNames Builtin.context
                  <> programConstrNames resolved
          instCon v
            | v `HS.member` constrs = Concrete.Con $ Left v
            | otherwise = pure v
          resolved' = bimap (>>>= instCon) (>>= instCon) <$> resolved
          groups = dependencyOrder resolved'
      case runTCM (process groups) mempty of
        (Left err, t) -> do
          mapM_ putStrLn t
          putStrLn err
        (Right res, _) -> do
          forM_ (concat res) $ \(_, b) -> do
            Text.putStrLn ""
            Text.putStrLn b
          Text.putStrLn "\ninit:"
          forM_ (concat res) $ \(i, _) ->
            unless (Text.null i) $ Text.putStrLn i
  where
    process groups = do
      addContext Builtin.context
      mapM (processGroup . fmap (\(n, (d, t)) -> (n, d, t))) groups

main :: IO ()
main = do
  x:_ <- getArgs
  processFile x
