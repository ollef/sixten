{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Processor where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Data.Bifunctor
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
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
import qualified Backend.ExtractExtern as ExtractExtern
import qualified Backend.Generate as Generate
import Backend.Lift
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
import qualified Syntax.Sized.Definition as Sized
import qualified Syntax.Sized.Extracted as Extracted
import qualified Syntax.Sized.Lifted as Lifted
import qualified Syntax.Sized.SLambda as SLambda
import Util
import VIX

processResolved
  :: HashMap Name (Definition Abstract.Expr Void, Abstract.Type Void)
  -> HashMap Name (SourceLoc, Unscoped.Definition Name, Unscoped.Type Name)
  -> VIX [Generate.Generated Text]
processResolved context
  = pure . ScopeCheck.scopeCheckProgram context
  >>=> processGroup

processGroup
  :: [(Name, SourceLoc, Concrete.PatDefinition Concrete.Expr Void, Concrete.Expr Void)]
  -> VIX [Generate.Generated Text]
processGroup
  = prettyConcreteGroup "Concrete syntax" absurd
  >=> typeCheckGroup
  >=> prettyTypedGroup "Abstract syntax" absurd
  >=> simplifyGroup
  >=> prettyTypedGroup "Simplified" absurd
  >=> processAbstractGroup

processAbstractGroup
  :: [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> VIX [Generate.Generated Text]
processAbstractGroup
  = addGroupToContext

  >=> slamGroup
  >=> prettyGroup "SLammed" vac

  >=> denatGroup
  >=> prettyGroup "Denaturalised" vac

  >=> closeGroup
  >=> prettyGroup "Closed" vac

  >=> liftGroup
  >>=> prettyGroup "Lambda-lifted" vac

  >=> closureConvertGroup
  >=> prettyGroup "Closure-converted" vac

  >=> processConvertedGroup
  where
    vac :: Functor e => e Void -> e Name
    vac = vacuous

processConvertedGroup
  :: [(Name, Sized.Definition Closed.Expr Void)]
  -> VIX [Generate.Generated Text]
processConvertedGroup
  = liftConvertedGroup
  >>=> prettyGroup "Lambda-lifted (2)" vac

  >=> inferGroupDirections
  >=> addSignaturesToContext
  >=> prettyGroup "Directed (lifted)" vac

  >=> extractExternGroup
  >=> prettyGroup "Extern extracted" (vac . Extracted.moduleInnards)

  >=> generateGroup
  where
    vac :: Functor e => e Void -> e Name
    vac = vacuous

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
  :: Pretty p
  => Text
  -> (e -> p)
  -> [(Name, e)]
  -> VIX [(Name, e)]
prettyGroup str f defs = do
  whenVerbose 10 $ do
    VIX.log $ "----- " <> str <> " -----"
    forM_ defs $ \(n, d) -> do
      VIX.log
        $ showWide
        $ runPrettyM
        $ prettyM n <+> "=" <+> prettyM (f d)
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
  -> VIX [[(Name, Sized.Definition Lifted.Expr Void)]]
liftGroup defs = fmap (Sized.dependencyOrder . concat) $ forM defs $ \(name, e) -> do
  let (e', fs) = liftToDefinition name e
  return $ (name, e') : fmap (second $ Sized.FunctionDef Private Sized.NonClosure) fs

closureConvertGroup
  :: [(Name, Sized.Definition Lifted.Expr Void)]
  -> VIX [(Name, Sized.Definition Closed.Expr Void)]
closureConvertGroup = ClosureConvert.convertDefinitions

liftConvertedGroup
  :: [(Name, Sized.Definition Closed.Expr Void)]
  -> VIX [[(Name, Sized.Definition Lifted.Expr Void)]]
liftConvertedGroup defs = fmap (Sized.dependencyOrder . concat) $ forM defs $ \(name, e) -> do
  let (e', fs) = liftClosures name e
  return $ (name, e') : fmap (second $ Sized.FunctionDef Private Sized.IsClosure) fs

inferGroupDirections
  :: [(Name, Sized.Definition Lifted.Expr Void)]
  -> VIX [(Name, Sized.Definition Lifted.Expr Void, Signature ReturnIndirect)]
inferGroupDirections
  = fmap Vector.toList . ReturnDirection.inferRecursiveDefs . Vector.fromList

addSignaturesToContext
  :: [(Name, Sized.Definition Lifted.Expr Void, Signature ReturnIndirect)]
  -> VIX [(Name, Sized.Definition Lifted.Expr Void)]
addSignaturesToContext defs = do
  let sigs = HashMap.fromList [(n, sig) | (n, _, sig) <- defs]
  logShow 11 "signatures" sigs
  addSignatures sigs
  return [(n, def) | (n, def, _) <- defs]

extractExternGroup
  :: [(Name, Sized.Definition Lifted.Expr Void)]
  -> VIX [(Name, Extracted.Module (Sized.Definition Extracted.Expr Void))]
extractExternGroup defs = return $
  flip map defs $ \(n, d) -> (n, ExtractExtern.extractDef n d)

generateGroup
  :: [(Name, Extracted.Module (Sized.Definition Extracted.Expr Void))]
  -> VIX [Generate.Generated Text]
generateGroup defs = do
  -- TODO compile the rest of the module
  target <- gets vixTarget
  qcindex <- qconstructorIndex
  sigs <- gets vixSignatures
  let env = Generate.GenEnv qcindex (`HashMap.lookup` sigs)
  return $ flip map defs $ \(x, m) -> Generate.runGen
    env
    (Generate.generateDefinition x $ vacuous $ Extracted.moduleInnards m)
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
  builtinParseResult <- Parse.parseFromFileEx Parse.program =<< getDataFileName "rts/Builtin.vix"
  parseResult <- Parse.parseFromFileEx Parse.program file
  let resolveResult = Resolve.program <$> ((<>) <$> builtinParseResult <*> parseResult)
  case resolveResult of
    Trifecta.Failure xs -> return $ Error $ SyntaxError xs
    Trifecta.Success (ExceptT (Identity (Left err))) -> return $ Error $ ResolveError err
    Trifecta.Success (ExceptT (Identity (Right resolved))) -> do
      procRes <- runVIX (process resolved) target logHandle verbosity
      case procRes of
        Left err -> return $ Error $ TypeError $ Text.pack err
        Right res -> withFile output WriteMode $ \handle -> do
          Generate.writeLlvmModule res handle
          return Success
  where
    context = Builtin.context target
    process resolved = do
      addContext context
      addConvertedSignatures $ Builtin.convertedSignatures target
      builtins <- processConvertedGroup $ HashMap.toList $ Builtin.convertedContext target
      results <- processResolved context resolved
      return $ builtins ++ results
