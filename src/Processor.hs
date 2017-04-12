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

import Analysis.Denat
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
import qualified Syntax.Sized.Lifted as Lifted
import qualified Syntax.Sized.SLambda as SLambda
import Util
import VIX

processResolved
  :: HashMap Name (Definition Abstract.Expr Void, Abstract.Type Void)
  -> HashMap Name (SourceLoc, Unscoped.Definition Name, Unscoped.Type Name)
  -> VIX [(LLVM.B, LLVM.B)]
processResolved context
  = pure . ScopeCheck.scopeCheckProgram context
  >>=> processGroup

processGroup
  :: [(Name, SourceLoc, Concrete.PatDefinition Concrete.Expr Void, Concrete.Expr Void)]
  -> VIX [(LLVM.B, LLVM.B)]
processGroup
  = prettyConcreteGroup "Concrete syntax" absurd
  >=> typeCheckGroup
  >=> prettyTypedGroup "Abstract syntax" absurd
  >=> simplifyGroup
  >=> prettyTypedGroup "Simplified" absurd
  >=> processAbstractGroup

processAbstractGroup
  :: [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> VIX [(LLVM.B, LLVM.B)]
processAbstractGroup
  = addGroupToContext

  >=> slamGroup
  >=> prettyGroup "SLammed" absurd

  >=> denatGroup
  >=> prettyGroup "Denaturalised" absurd

  >=> closeGroup
  >=> prettyGroup "Closed" absurd

  >=> liftGroup
  >>=> prettyGroup "Lambda-lifted" absurd

  >=> closureConvertGroup
  >=> prettyGroup "Closure-converted" absurd

  >=> processConvertedGroup

processConvertedGroup
  :: [(Name, Lifted.Definition Closed.Expr Void)]
  -> VIX [(LLVM.B, LLVM.B)]
processConvertedGroup
  = liftConvertedGroup
  >>=> prettyGroup "Lambda-lifted (2)" absurd

  >=> inferGroupDirections
  >=> addSignaturesToContext
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
  -> VIX [(Name, SourceLoc, Concrete.PatDefinition e v, e v)]
prettyConcreteGroup str f defs = do
  whenVerbose 10 $ do
    VIX.log $ "----- " <> str <> " -----"
    forM_ defs $ \(n, _, d, t) -> do
      let t' = f <$> t
      VIX.log
        $ showWide
        $ runPrettyM
        $ prettyM n <+> ":" <+> prettyM t'
      VIX.log
        $ showWide
        $ runPrettyM
        $ prettyM (f <$> d)
      VIX.log ""
  return defs

prettyLocatedGroup
  :: (Pretty (e Name), Eq1 e, Syntax e)
  => Text
  -> (v -> Name)
  -> [(Name, x, Definition e v, e v)]
  -> VIX [(Name, x, Definition e v, e v)]
prettyLocatedGroup x f defs = do
  void $ prettyTypedGroup x f $ (\(n, _, d, t) -> (n, d, t)) <$> defs
  return defs

prettyTypedGroup
  :: (Pretty (e Name), Eq1 e, Syntax e)
  => Text
  -> (v -> Name)
  -> [(Name, Definition e v, e v)]
  -> VIX [(Name, Definition e v, e v)]
prettyTypedGroup str f defs = do
  whenVerbose 10 $ do
    VIX.log $ "----- " <> str <> " -----"
    forM_ defs $ \(n, d, t) -> do
      let t' = f <$> t
      VIX.log
        $ showWide
        $ runPrettyM
        $ prettyM n <+> ":" <+> prettyM t'
      VIX.log
        $ showWide
        $ runPrettyM
        $ prettyM n <+> "=" <+> prettyTypedDef (f <$> d) t'
      VIX.log ""
  return defs

prettyGroup
  :: (Pretty (e Name), Functor e)
  => Text
  -> (v -> Name)
  -> [(Name, e v)]
  -> VIX [(Name, e v)]
prettyGroup str f defs = do
  whenVerbose 10 $ do
    VIX.log $ "----- " <> str <> " -----"
    forM_ defs $ \(n, d) -> do
      VIX.log
        $ showWide
        $ runPrettyM
        $ prettyM n <+> "=" <+> prettyM (f <$> d)
      VIX.log ""
  return defs

typeCheckGroup
  :: [(Name, SourceLoc, Concrete.PatDefinition Concrete.Expr Void, Concrete.Expr Void)]
  -> VIX [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
typeCheckGroup
  = fmap Vector.toList . TypeCheck.checkRecursiveDefs . Vector.fromList

simplifyGroup
  :: [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> VIX [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
simplifyGroup defs = forM defs $ \(x, def, typ) ->
  return (x, simplifyDef globTerm def, simplifyExpr globTerm 0 typ)
  where
    globTerm x = not $ HashSet.member x names
    names = HashSet.fromList $ fst3 <$> defs

addGroupToContext
  :: [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> VIX [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
addGroupToContext defs = do
  addContext $ HashMap.fromList $ (\(n, d, t) -> (n, (d, t))) <$> defs
  return defs

slamGroup
  :: [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> VIX [(Name, SLambda.Expr Void)]
slamGroup defs = forM defs $ \(x, d, _t) -> do
  d' <- SLam.slamDef $ vacuous d
  d'' <- traverse (throwError . ("slamGroup " ++) . show) d'
  return (x, d'')

denatGroup
  :: [(Name, SLambda.Expr Void)]
  -> VIX [(Name, SLambda.Expr Void)]
denatGroup defs = return [(n, denat def) | (n, def) <- defs]

closeGroup
  :: [(Name, SLambda.Expr Void)]
  -> VIX [(Name, Closed.Expr Void)]
closeGroup defs = forM defs $ \(x, e) -> do
  e' <- closeExpr $ vacuous e
  e'' <- traverse (throwError . ("closeGroup " ++) . show) e'
  return (x, e'')

liftGroup
  :: [(Name, Closed.Expr Void)]
  -> VIX [[(Name, Lifted.Definition Lifted.Expr Void)]]
liftGroup defs = fmap (Lifted.dependencyOrder . concat) $ forM defs $ \(name, e) -> do
  let (e', fs) = liftToDefinition name e
  return $ (name, e') : fmap (second $ Lifted.FunctionDef Private Lifted.NonClosure) fs

closureConvertGroup
  :: [(Name, Lifted.Definition Lifted.Expr Void)]
  -> VIX [(Name, Lifted.Definition Closed.Expr Void)]
closureConvertGroup = ClosureConvert.convertDefinitions

liftConvertedGroup
  :: [(Name, Lifted.Definition Closed.Expr Void)]
  -> VIX [[(Name, Lifted.Definition Lifted.Expr Void)]]
liftConvertedGroup defs = fmap (Lifted.dependencyOrder . concat) $ forM defs $ \(name, e) -> do
  let (e', fs) = liftClosures name e
  return $ (name, e') : fmap (second $ Lifted.FunctionDef Private Lifted.IsClosure) fs

inferGroupDirections
  :: [(Name, Lifted.Definition Lifted.Expr Void)]
  -> VIX [(Name, Lifted.Definition Lifted.Expr Void, Signature ReturnIndirect)]
inferGroupDirections
  = fmap Vector.toList . ReturnDirection.inferRecursiveDefs . Vector.fromList

addSignaturesToContext
  :: [(Name, Lifted.Definition Lifted.Expr Void, Signature ReturnIndirect)]
  -> VIX [(Name, Lifted.Definition Lifted.Expr Void)]
addSignaturesToContext defs = do
  let sigs = HashMap.fromList [(n, sig) | (n, _, sig) <- defs]
  logShow 11 "signatures" sigs
  addSignatures sigs
  return [(n, def) | (n, def, _) <- defs]

generateGroup
  :: [(Name, Lifted.Definition Lifted.Expr Void)]
  -> VIX [(LLVM.B, LLVM.B)]
generateGroup defs = do
  target <- gets vixTarget
  qcindex <- qconstructorIndex
  sigs <- gets vixSignatures
  let env = Generate.GenEnv qcindex (`HashMap.lookup` sigs)
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
      procRes <- runVIX (process resolved) target logHandle verbosity
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
    context = Builtin.context target
    convertedSignatures = Builtin.convertedSignatures target
    convertedContext = Builtin.convertedContext target
    process resolved = do
      addContext context
      addConvertedSignatures convertedSignatures
      builtins <- processConvertedGroup $ HashMap.toList convertedContext
      results <- processResolved context resolved
      return $ builtins ++ results
