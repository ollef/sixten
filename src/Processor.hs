{-# LANGUAGE OverloadedStrings #-}
module Processor where

import qualified Bound.Scope.Simple as Simple
import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import Data.Monoid
import Data.Text(Text)
import qualified Data.Text as Text
import qualified Data.Text.Lazy.IO as LazyText
import qualified Data.Text.IO as Text
import qualified Data.Vector as V
import Data.Void
import Prelude.Extras
import System.IO

import qualified Builtin
import Close
import ClosureConvert
import Erase
import qualified Generate
import Infer
import Lift
import qualified LLVM
import Meta
import Simplify
import TCM
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Closed as Closed
import qualified Syntax.Concrete as Concrete
import qualified Syntax.Converted as Converted
import qualified Syntax.Lifted as Lifted
import qualified Syntax.Parse as Parse
import qualified Syntax.Resolve as Resolve
import qualified Syntax.SLambda as SLambda
import Util

processGroup
  :: [(Name, Definition Concrete.Expr Name, Concrete.Expr Name)]
  -> TCM [(Name, LLVM.B)]
processGroup
  = prettyTypedGroup "Concrete syntax" id
  >=> exposeGroup
  >=> typeCheckGroup
  >=> prettyTypedGroup "Abstract syntax" absurd
  >=> simplifyGroup
  >=> prettyTypedGroup "Simplified" absurd
  >=> addGroupToContext
  >=> eraseGroup
  >=> prettyGroup "Erased (SLambda)" absurd
  >=> closeGroup
  >=> prettyGroup "Closed" absurd
  >=> closureConvertGroup
  >=> prettyGroup "Closure-converted" absurd
  >=> processConvertedGroup

processConvertedGroup
  :: [(Name, Converted.SExpr Void)]
  -> TCM [(Name, LLVM.B)]
processConvertedGroup
  = liftGroup
  >=> prettyGroup "Lambda-lifted" absurd
  >=> generateGroup

prettyTypedGroup
  :: (Pretty (e Name), Functor e, Eq1 e, SyntaxPi e)
  => Text
  -> (v -> Name)
  -> [(Name, Definition e v, e v)]
  -> TCM [(Name, Definition e v, e v)]
prettyTypedGroup str f defs = do
  liftIO $ Text.putStrLn $ "----- " <> str <> " -----"
  forM_ defs $ \(n, d, t) -> liftIO $ do
    let t' = f <$> t
    LazyText.putStrLn
      $ showWide
      $ runPrettyM
      $ prettyM n <+> ":" <+> prettyM t'
    LazyText.putStrLn
      $ showWide
      $ runPrettyM
      $ prettyM n <+> "=" <+> prettyTypedDef (f <$> d) t'
    Text.putStrLn ""
  return defs

prettyGroup
  :: (Pretty (e Name), Functor e)
  => Text
  -> (v -> Name)
  -> [(Name, e v)]
  -> TCM [(Name, e v)]
prettyGroup str f defs = do
  liftIO $ Text.putStrLn $ "----- " <> str <> " -----"
  forM_ defs $ \(n, d) -> liftIO $ do
    LazyText.putStrLn
      $ showWide
      $ runPrettyM
      $ prettyM n <+> "=" <+> prettyM (f <$> d)
    Text.putStrLn ""
  return defs

exposeGroup
  :: [(Name, Definition Concrete.Expr Name, Concrete.Expr Name)]
  -> TCM [(Name, Definition Concrete.Expr (Var Int v), Scope Int Concrete.Expr v)]
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
  :: [(Name, Definition Concrete.Expr (Var Int (MetaVar Abstract.Expr)), ScopeM Int Concrete.Expr)]
  -> TCM [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
typeCheckGroup defs = do
  checkedDefs <- checkRecursiveDefs $ V.fromList defs

  let vf :: MetaVar Abstract.Expr -> TCM b
      vf v = throwError $ "typeCheckGroup " ++ show v
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

simplifyGroup
  :: [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> TCM [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
simplifyGroup defs = forM defs $ \(x, def, typ) -> do
  def' <- simplifyDef $ vacuous def
  def'' <- traverse (throwError . ("simplifyGroup " ++) . show) def'
  return (x, def'', typ)

addGroupToContext
  :: [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> TCM [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
addGroupToContext defs = do
  addContext $ HM.fromList $ (\(n, d, t) -> (n, (d, t))) <$> defs
  return defs

eraseGroup
  :: [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)] 
  -> TCM [(Name, SLambda.SExpr Void)]
eraseGroup defs = sequence
  [ do
      d' <- eraseDef (vacuous d) (vacuous t)
      d'' <- traverse (throwError . ("eraseGroup " ++) . show) d'
      return (x, d'')
  | (x, d, t) <- defs
  ]

closeGroup
  :: [(Name, SLambda.SExpr Void)]
  -> TCM [(Name, Closed.SExpr Void)]
closeGroup defs = forM defs $ \(x, e) -> do
  e' <- closeSExpr $ vacuous e
  e'' <- traverse (throwError . ("closeGroup " ++) . show) e'
  return (x, e'')

closureConvertGroup
  :: [(Name, Closed.SExpr Void)]
  -> TCM [(Name, Converted.SExpr Void)]
closureConvertGroup defs = do
  sigs <- forM defs $ \(x, e) -> (,) x <$> ClosureConvert.createSignature (vacuous e)
  addConvertedSignatures $ HM.fromList sigs
  forM sigs $ \(x, sig) ->
    (,) x . fmap (error "closureConvertGroup conv") <$> ClosureConvert.convertSignature (error "closureConvertGroup sig" <$> sig)

liftGroup
  :: [(Name, Converted.SExpr Void)]
  -> TCM [(Name, Lifted.Definition Void)]
liftGroup defs = fmap concat $ forM defs $ \(name, e) -> do
  let (e', fs) = liftDefinition name e
  addConvertedSignatures $ HM.fromList $ fmap fakeSignature <$> fs
  return $ (name, e') : fmap (second $ Lifted.FunctionDef Private) fs
  where
    -- TODO this isn't a very nice way to do this
    fakeSignature
      :: Lifted.Function Void
      -> Converted.Signature Converted.Expr Unit Void
    fakeSignature (Lifted.Function retDir tele _body)
      = Converted.Function
        retDir
        (Telescope $ (\(h, d) -> (h, d, Simple.Scope $ Converted.Lit 0)) <$> tele)
        $ Simple.Scope Unit

generateGroup
  :: [(Name, Lifted.Definition Void)]
  -> TCM [(LLVM.B, LLVM.B)]
generateGroup defs = do
  qcindex <- qconstructorIndex
  cxt <- gets tcConvertedSignatures
  let env = Generate.GenEnv qcindex (`HM.lookup` cxt)
  return $ flip map defs $ \(x, e) ->
    second (fold . intersperse "\n")
      $ Generate.runGen env
      $ Generate.generateDefinition x
      $ vacuous e

processFile :: FilePath -> FilePath -> FilePath -> IO ()
processFile file output logFile = do
  parseResult <- Parse.parseFromFile Parse.program file
  let resolveResult = Resolve.program <$> parseResult
  case resolveResult of
    Nothing -> return ()
    Just (Left err) -> do
      Text.putStrLn err
      error "Syntax error"
    Just (Right resolved) -> do
      let groups = filter (not . null) $ dependencyOrder
            (HS.map (either id (\(QConstr n _) -> n)) . Concrete.constructors) resolved
          constrs = HS.fromList
                  $ programConstrNames Builtin.context
                  <> programConstrNames resolved
          instCon v
            | v `HS.member` constrs = Concrete.Con $ Left v
            | otherwise = pure v
          groups' = fmap (fmap $ bimap (>>>= instCon) (>>= instCon)) <$> groups
      procRes <- withFile logFile WriteMode $ \handle ->
        runTCM (process groups') mempty handle
      case procRes of
        Left err -> do
          putStrLn err
          error "Error"
        Right res -> do
          forwardDecls <- Text.readFile "test/forwarddecls.ll"
          withFile output WriteMode $ \handle -> do
            let outputStrLn = Text.hPutStrLn handle
            outputStrLn forwardDecls
            forM_ (concat res) $ \(_, b) -> do
              outputStrLn ""
              outputStrLn b
            outputStrLn ""
            outputStrLn "define i32 @main() {"
            outputStrLn "  call void @GC_init()"
            forM_ (concat res) $ \(i, _) ->
              unless (Text.null i) $ outputStrLn i
            outputStrLn "  ret i32 0"
            outputStrLn "}"
  where
    process groups = do
      addContext Builtin.context
      addConvertedSignatures $ Converted.signature <$> Builtin.convertedContext
      builtins <- processConvertedGroup $ HM.toList Builtin.convertedContext
      results <- mapM (processGroup . fmap (\(n, (d, t)) -> (n, d, t))) groups
      return $ builtins : results
