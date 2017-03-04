{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Processor where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Data.Bifunctor
import Data.Foldable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.List
import Data.Monoid
import Data.Text(Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Data.Vector as Vector
import Data.Void
import Prelude.Extras
import System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen
import qualified Text.Trifecta as Trifecta

import qualified Analysis.ReturnDirection as ReturnDirection
import Analysis.Simplify
import Backend.Close
import qualified Backend.ClosureConvert as ClosureConvert
import qualified Backend.Generate as Generate
import Backend.Lift
import qualified Backend.LLVM as LLVM
import qualified Backend.SLam as SLam
import Backend.Target
import qualified Builtin
import qualified Frontend.Parse as Parse
import qualified Frontend.Resolve as Resolve
import qualified Frontend.ScopeCheck as ScopeCheck
import qualified Inference.TypeCheck as TypeCheck
import Paths_sixten
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete.Scoped as Concrete
import qualified Syntax.Concrete.Unscoped as Unscoped
import qualified Syntax.Sized.Closed as Closed
import qualified Syntax.Sized.Converted as Converted
import qualified Syntax.Sized.Lifted as Lifted
import qualified Syntax.Sized.SLambda as SLambda
import TCM
import Util

processResolved
  :: HashMap Name (SourceLoc, Unscoped.Definition Name, Unscoped.Type Name)
  -> TCM [(LLVM.B, LLVM.B)]
processResolved
  = pure . ScopeCheck.scopeCheckProgram
  >>=> processGroup

processGroup
  :: [(Name, SourceLoc, Concrete.PatDefinition Concrete.Expr Void, Concrete.Expr Void)]
  -> TCM [(LLVM.B, LLVM.B)]
processGroup
  = prettyConcreteGroup "Concrete syntax" absurd
  >=> typeCheckGroup
  >=> prettyTypedGroup "Abstract syntax" absurd
  >=> simplifyGroup
  >=> prettyTypedGroup "Simplified" absurd
  >=> processAbstractGroup

processAbstractGroup
  :: [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> TCM [(LLVM.B, LLVM.B)]
processAbstractGroup
  = addGroupToContext
  >=> slamGroup
  >=> prettyGroup "SLammed:" absurd
  >=> closeGroup
  >=> prettyGroup "Closed" absurd
  >=> closureConvertGroup
  >=> prettyGroup "Closure-converted" absurd
  >=> processConvertedGroup

processConvertedGroup
  :: [(Name, Converted.Expr Void)]
  -> TCM [(LLVM.B, LLVM.B)]
processConvertedGroup
  = liftGroup
  >>=> prettyGroup "Lambda-lifted" absurd
  >=> inferGroupDirections
  >=> addReturnDirectionsToContext
  >=> prettyGroup "Directed (lifted)" absurd
  >=> generateGroup

infixr 1 >>=>
(>>=>) :: Monad m => (a -> m [b]) -> (b -> m [c]) -> a -> m [c]
(f >>=> g) a = concat <$> (f a >>= mapM g)

prettyConcreteGroup
  :: (Pretty (e Name), Monad e, Traversable e)
  => Text
  -> (v -> Name)
  -> [(Name, SourceLoc, Concrete.PatDefinition e v, e v)]
  -> TCM [(Name, SourceLoc, Concrete.PatDefinition e v, e v)]
prettyConcreteGroup str f defs = do
  whenVerbose 10 $ do
    TCM.log $ "----- " <> str <> " -----"
    forM_ defs $ \(n, _, d, t) -> do
      let t' = f <$> t
      TCM.log
        $ showWide
        $ runPrettyM
        $ prettyM n <+> ":" <+> prettyM t'
      TCM.log
        $ showWide
        $ runPrettyM
        $ prettyM (f <$> d)
      TCM.log ""
  return defs

prettyLocatedGroup
  :: (Pretty (e Name), Eq1 e, Syntax e)
  => Text
  -> (v -> Name)
  -> [(Name, x, Definition e v, e v)]
  -> TCM [(Name, x, Definition e v, e v)]
prettyLocatedGroup x f defs = do
  void $ prettyTypedGroup x f $ (\(n, _, d, t) -> (n, d, t)) <$> defs
  return defs

prettyTypedGroup
  :: (Pretty (e Name), Eq1 e, Syntax e)
  => Text
  -> (v -> Name)
  -> [(Name, Definition e v, e v)]
  -> TCM [(Name, Definition e v, e v)]
prettyTypedGroup str f defs = do
  whenVerbose 10 $ do
    TCM.log $ "----- " <> str <> " -----"
    forM_ defs $ \(n, d, t) -> do
      let t' = f <$> t
      TCM.log
        $ showWide
        $ runPrettyM
        $ prettyM n <+> ":" <+> prettyM t'
      TCM.log
        $ showWide
        $ runPrettyM
        $ prettyM n <+> "=" <+> prettyTypedDef (f <$> d) t'
      TCM.log ""
  return defs

prettyGroup
  :: (Pretty (e Name), Functor e)
  => Text
  -> (v -> Name)
  -> [(Name, e v)]
  -> TCM [(Name, e v)]
prettyGroup str f defs = do
  whenVerbose 10 $ do
    TCM.log $ "----- " <> str <> " -----"
    forM_ defs $ \(n, d) -> do
      TCM.log
        $ showWide
        $ runPrettyM
        $ prettyM n <+> "=" <+> prettyM (f <$> d)
      TCM.log ""
  return defs

typeCheckGroup
  :: [(Name, SourceLoc, Concrete.PatDefinition Concrete.Expr Void, Concrete.Expr Void)]
  -> TCM [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
typeCheckGroup
  = fmap Vector.toList . TypeCheck.checkRecursiveDefs . Vector.fromList

simplifyGroup
  :: [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> TCM [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
simplifyGroup defs = forM defs $ \(x, def, typ) ->
  return (x, simplifyDef globTerm def, simplifyExpr globTerm 0 typ)
  where
    globTerm x = not $ HashSet.member x names
    names = HashSet.fromList $ fst3 <$> defs

addGroupToContext
  :: [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> TCM [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
addGroupToContext defs = do
  addContext $ HashMap.fromList $ (\(n, d, t) -> (n, (d, t))) <$> defs
  return defs

slamGroup
  :: [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> TCM [(Name, SLambda.Expr Void)]
slamGroup defs = sequence
  [ do
      d' <- SLam.slamDef $ vacuous d
      d'' <- traverse (throwError . ("slamGroup " ++) . show) d'
      return (x, d'')
  | (x, d, _t) <- defs
  ]

closeGroup
  :: [(Name, SLambda.Expr Void)]
  -> TCM [(Name, Closed.Expr Void)]
closeGroup defs = forM defs $ \(x, e) -> do
  e' <- closeExpr $ vacuous e
  e'' <- traverse (throwError . ("closeGroup " ++) . show) e'
  return (x, e'')

closureConvertGroup
  :: [(Name, Closed.Expr Void)]
  -> TCM [(Name, Converted.Expr Void)]
closureConvertGroup defs = do
  sigs <- forM defs $ \(x, e) -> (,) x <$> ClosureConvert.createSignature (vacuous e)
  addConvertedSignatures $ HashMap.fromList sigs
  forM sigs $ \(x, sig) ->
    (,) x . fmap (error "closureConvertGroup conv") <$> ClosureConvert.convertSignature (error "closureConvertGroup sig" <$> sig)

liftGroup
  :: [(Name, Converted.Expr Void)]
  -> TCM [[(Name, Lifted.Definition ClosureDir (Lifted.Expr ClosureDir) Void)]]
liftGroup defs = fmap (Lifted.dependencyOrder . concat) $ forM defs $ \(name, e) -> do
  let (e', fs) = liftDefinition name e
  addConvertedSignatures $ HashMap.fromList $ fmap Lifted.signature <$> fs
  return $ (name, e') : fmap (second $ Lifted.FunctionDef Private) fs

inferGroupDirections
  :: [(Name, Lifted.Definition ClosureDir (Lifted.Expr ClosureDir) Void)]
  -> TCM [(Name, Lifted.Definition RetDir (Lifted.Expr RetDir) Void)]
inferGroupDirections
  = fmap Vector.toList . ReturnDirection.inferRecursiveDefs . Vector.fromList

addReturnDirectionsToContext
  :: [(Name, Lifted.Definition RetDir (Lifted.Expr RetDir) Void)]
  -> TCM [(Name, Lifted.Definition RetDir (Lifted.Expr RetDir) Void)]
addReturnDirectionsToContext defs = do
  addReturnDirections [(n, retDir) | (n, Lifted.FunctionDef _ (Lifted.Function retDir _ _)) <- defs]
  return defs

generateGroup
  :: [(Name, Lifted.Definition RetDir (Lifted.Expr RetDir) Void)]
  -> TCM [(LLVM.B, LLVM.B)]
generateGroup defs = do
  target <- gets tcTarget
  qcindex <- qconstructorIndex
  sigs <- gets tcConvertedSignatures
  retDirs <- gets tcReturnDirections
  let env = Generate.GenEnv qcindex (`HashMap.lookup` sigs) (`HashMap.lookup` retDirs)
  return $ flip map defs $ \(x, e) ->
    bimap (($ LLVM.targetConfig target) . LLVM.unC) (fold . intersperse "\n")
      $ Generate.runGen
        env
        (Generate.generateDefinition x $ vacuous e)
        target

data Error
  = SyntaxError Doc
  | ResolveError Text
  | TypeError Text
  | CommandLineError Doc
  deriving Show

printError :: Error -> IO ()
printError err = case err of
  SyntaxError doc -> do
    Text.putStrLn "Syntax error"
    Leijen.displayIO stdout
      $ Leijen.renderPretty 0.8 80
      $ doc <> Leijen.linebreak
  ResolveError s -> do
    Text.putStrLn "Syntax error"
    Text.putStrLn s
  TypeError s -> do
    Text.putStrLn "Type error"
    Text.putStrLn s
  CommandLineError doc -> do
    Text.putStrLn "Command-line error"
    Leijen.displayIO stdout
      $ Leijen.renderPretty 0.8 80
      $ doc <> Leijen.linebreak

data Result
  = Error Error
  | Success
  deriving Show

processFile :: FilePath -> FilePath -> Target -> Handle -> Int -> IO Result
processFile file output target logHandle verbosity = do
  parseResult <- Parse.parseFromFileEx Parse.program file
  let resolveResult = Resolve.program <$> parseResult
  case resolveResult of
    Trifecta.Failure xs -> return $ Error $ SyntaxError xs
    Trifecta.Success (ExceptT (Identity (Left err))) -> return $ Error $ ResolveError err
    Trifecta.Success (ExceptT (Identity (Right resolved))) -> do
      procRes <- runTCM (process resolved) target logHandle verbosity
      case procRes of
        Left err -> return $ Error $ TypeError $ Text.pack err
        Right res -> do
          forwardDecls <- Text.readFile =<< getDataFileName "rts/forwarddecls.ll"
          withFile output WriteMode $ \handle -> do
            let outputStrLn = Text.hPutStrLn handle
            outputStrLn forwardDecls
            forM_ res $ \(_, b) -> do
              outputStrLn ""
              outputStrLn b
            outputStrLn ""
            outputStrLn "define i32 @main() {"
            outputStrLn "  call void @GC_init()"
            forM_ res $ \(i, _) ->
              unless (Text.null i) $ outputStrLn i
            outputStrLn "  ret i32 0"
            outputStrLn "}"
          return Success
  where
    process resolved = do
      addContext Builtin.context
      addConvertedSignatures $ Converted.signature <$> Builtin.convertedContext
      builtins <- processConvertedGroup $ HashMap.toList Builtin.convertedContext
      results <- processResolved resolved
      return $ builtins ++ results
