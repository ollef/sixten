{-# LANGUAGE OverloadedStrings #-}
-- TODO rename to Module?
module Processor.File where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Data.Bifunctor
import Data.Functor.Classes
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.Maybe
import Data.Monoid
import Data.Text(Text)
import qualified Data.Text.IO as Text
import qualified Data.Vector as Vector
import Data.Void
import System.IO
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
import qualified Frontend.Parse as Parse
import qualified Frontend.Resolve as Resolve
import qualified Frontend.ScopeCheck as ScopeCheck
import qualified Inference.TypeCheck as TypeCheck
import Processor.Result
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

-- TODO: Clean this up
type DependencySigs = HashMap QName Text

processResolved
  :: Module (HashMap QName (SourceLoc, Unscoped.Definition QName, Unscoped.Type QName))
  -> VIX [Extracted.Submodule (Generate.Generated (Text, DependencySigs))]
processResolved
  = scopeCheckProgram
  >=> mapM (prettyConcreteGroup "Concrete syntax" absurd)
  >>=> processGroup

processGroup
  :: [(QName, SourceLoc, Concrete.PatDefinition Concrete.Expr Void, Concrete.Expr Void)]
  -> VIX [Extracted.Submodule (Generate.Generated (Text, DependencySigs))]
processGroup
  = prettyConcreteGroup "Concrete syntax" absurd
  >=> typeCheckGroup

  >=> prettyTypedGroup "Abstract syntax" absurd

  >=> simplifyGroup
  >=> prettyTypedGroup "Simplified" absurd

  >=> addGroupToContext

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
  :: [(QName, Sized.Definition Closed.Expr Void)]
  -> VIX [Extracted.Submodule (Generate.Generated (Text, DependencySigs))]
processConvertedGroup
  = liftConvertedGroup
  >>=> prettyGroup "Lambda-lifted (2)" vac

  >=> inferGroupDirections
  >=> addSignaturesToContext
  >=> prettyGroup "Directed (lifted)" vac

  >=> extractExternGroup
  >=> prettyGroup "Extern extracted" (vac . Extracted.submoduleContents)

  >=> generateGroup
  where
    vac :: Functor e => e Void -> e Name
    vac = vacuous

infixr 1 >>=>
(>>=>) :: Monad m => (a -> m [b]) -> (b -> m [c]) -> a -> m [c]
(f >>=> g) a = concat <$> (f a >>= mapM g)

prettyConcreteGroup
  :: (Pretty (e QName), Monad e, Traversable e)
  => Text
  -> (v -> QName)
  -> [(QName, SourceLoc, Concrete.PatDefinition e v, e v)]
  -> VIX [(QName, SourceLoc, Concrete.PatDefinition e v, e v)]
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
  :: (Pretty (e QName), Eq1 e, Syntax e)
  => Text
  -> (v -> QName)
  -> [(QName, x, Definition e v, e v)]
  -> VIX [(QName, x, Definition e v, e v)]
prettyLocatedGroup x f defs = do
  void $ prettyTypedGroup x f $ (\(n, _, d, t) -> (n, d, t)) <$> defs
  return defs

prettyTypedGroup
  :: (Pretty (e QName), Eq1 e, Syntax e)
  => Text
  -> (v -> QName)
  -> [(QName, Definition e v, e v)]
  -> VIX [(QName, Definition e v, e v)]
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
  -> [(QName, e)]
  -> VIX [(QName, e)]
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

scopeCheckProgram
  :: Module (HashMap QName (SourceLoc, Unscoped.Definition QName, Unscoped.Type QName))
  -> VIX [[(QName, SourceLoc, Concrete.PatDefinition Concrete.Expr Void, Concrete.Type Void)]]
scopeCheckProgram m = do
  res <- ScopeCheck.scopeCheckModule m
  let defNames = HashSet.fromMap $ void $ moduleContents m
      conNames = HashSet.fromList
        [ QConstr n c
        | (n, (_, Unscoped.DataDefinition _ d, _)) <- HashMap.toList $ moduleContents m
        , c <- constrName <$> d
        ]
  addModule (moduleName m) $ HashSet.map Right defNames <> HashSet.map Left conNames
  return res

typeCheckGroup
  :: [(QName, SourceLoc, Concrete.PatDefinition Concrete.Expr Void, Concrete.Expr Void)]
  -> VIX [(QName, Definition Abstract.Expr Void, Abstract.Expr Void)]
typeCheckGroup
  = fmap Vector.toList . TypeCheck.checkRecursiveDefs . Vector.fromList

simplifyGroup
  :: [(QName, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> VIX [(QName, Definition Abstract.Expr Void, Abstract.Expr Void)]
simplifyGroup defs = forM defs $ \(x, def, typ) ->
  return (x, simplifyDef globTerm def, simplifyExpr globTerm 0 typ)
  where
    globTerm x = not $ HashSet.member x names
    names = HashSet.fromList $ fst3 <$> defs

addGroupToContext
  :: [(QName, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> VIX [(QName, Definition Abstract.Expr Void, Abstract.Expr Void)]
addGroupToContext defs = do
  addContext $ HashMap.fromList $ (\(n, d, t) -> (n, (d, t))) <$> defs
  return defs

slamGroup
  :: [(QName, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> VIX [(QName, SLambda.Expr Void)]
slamGroup defs = forM defs $ \(x, d, _t) -> do
  d' <- SLam.slamDef $ vacuous d
  d'' <- traverse (throwError . ("slamGroup " ++) . show) d'
  return (x, d'')

denatGroup
  :: [(QName, SLambda.Expr Void)]
  -> VIX [(QName, SLambda.Expr Void)]
denatGroup defs = return [(n, denat def) | (n, def) <- defs]

closeGroup
  :: [(QName, SLambda.Expr Void)]
  -> VIX [(QName, Closed.Expr Void)]
closeGroup defs = forM defs $ \(x, e) -> do
  e' <- closeExpr $ vacuous e
  e'' <- traverse (throwError . ("closeGroup " ++) . show) e'
  return (x, e'')

liftGroup
  :: [(QName, Closed.Expr Void)]
  -> VIX [[(QName, Sized.Definition Lifted.Expr Void)]]
liftGroup defs = fmap (Sized.dependencyOrder . concat) $ forM defs $ \(name, e) -> do
  let (e', fs) = liftToDefinition name e
  return $ (name, e') : fmap (second $ Sized.FunctionDef Private Sized.NonClosure) fs

closureConvertGroup
  :: [(QName, Sized.Definition Lifted.Expr Void)]
  -> VIX [(QName, Sized.Definition Closed.Expr Void)]
closureConvertGroup = ClosureConvert.convertDefinitions

liftConvertedGroup
  :: [(QName, Sized.Definition Closed.Expr Void)]
  -> VIX [[(QName, Sized.Definition Lifted.Expr Void)]]
liftConvertedGroup defs = fmap (Sized.dependencyOrder . concat) $ forM defs $ \(name, e) -> do
  let (e', fs) = liftClosures name e
  return $ (name, e') : fmap (second $ Sized.FunctionDef Private Sized.IsClosure) fs

inferGroupDirections
  :: [(QName, Sized.Definition Lifted.Expr Void)]
  -> VIX [(QName, Sized.Definition Lifted.Expr Void, Signature ReturnIndirect)]
inferGroupDirections
  = fmap Vector.toList . ReturnDirection.inferRecursiveDefs . Vector.fromList

addSignaturesToContext
  :: [(QName, Sized.Definition Lifted.Expr Void, Signature ReturnIndirect)]
  -> VIX [(QName, Sized.Definition Lifted.Expr Void)]
addSignaturesToContext defs = do
  let sigs = HashMap.fromList [(n, sig) | (n, _, sig) <- defs]
  logShow 11 "signatures" sigs
  addSignatures sigs
  return [(n, def) | (n, def, _) <- defs]

extractExternGroup
  :: [(QName, Sized.Definition Lifted.Expr Void)]
  -> VIX [(QName, Extracted.Submodule (Sized.Definition Extracted.Expr Void))]
extractExternGroup defs = do
  target <- gets vixTarget
  return $
    flip map defs $ \(n, d) -> (n, ExtractExtern.extractDef n d target)

generateGroup
  :: [(QName, Extracted.Submodule (Sized.Definition Extracted.Expr Void))]
  -> VIX [Extracted.Submodule (Generate.Generated (Text, DependencySigs))]
generateGroup defs = do
  target <- gets vixTarget
  qcindex <- qconstructorIndex
  sigs <- gets vixSignatures
  let env = Generate.GenEnv qcindex (`HashMap.lookup` sigs)

  return
    [ Generate.generateModule env target x $ vacuous <$> m
    | (x, m) <- defs
    ]

data ProcessFileArgs = ProcessFileArgs
  { procFile :: FilePath
  , procLlOutput, procCOutput :: FilePath
  , procTarget :: Target
  , procLogHandle :: Handle
  , procVerbosity :: Int
  } deriving (Eq, Show)

writeModule
  :: Module [Extracted.Submodule (Generate.Generated (Text, DependencySigs))]
  -> FilePath
  -> [(Language, FilePath)]
  -> IO [(Language, FilePath)]
writeModule modul llOutputFile externOutputFiles = do
  let subModules = moduleContents modul
  withFile llOutputFile WriteMode $ do
    let decls
          = mconcat
          $ snd . Generate.generated . Extracted.submoduleContents <$> subModules
    Generate.writeLlvmModule
      (moduleName modul)
      (moduleImports modul)
      (fmap fst . Extracted.submoduleContents <$> subModules)
      decls
  fmap catMaybes $
    forM externOutputFiles $ \(lang, outFile) ->
      case ExtractExtern.moduleExterns lang (fmap (fmap fst) <$> subModules) of
        [] -> return Nothing
        externCode -> withFile outFile WriteMode $ \handle -> do
          -- TODO this is C specific
          Text.hPutStrLn handle "#include <stdint.h>"
          Text.hPutStrLn handle "#include <stdlib.h>"
          Text.hPutStrLn handle "#include <stdio.h>"
          forM_ externCode $ \code -> do
            Text.hPutStrLn handle ""
            Text.hPutStrLn handle code
          return $ Just (lang, outFile)

parse
  :: FilePath
  -> IO (Result (Module [(Parse.TopLevelParsed QName, Span)]))
parse file = do
  parseResult <- Parse.parseFromFileEx Parse.modul file
  case parseResult of
    Trifecta.Failure f -> return $ Failure $ pure $ SyntaxError $ Trifecta._errDoc f
    Trifecta.Success res -> return $ Success res

resolve
  :: Module [(Parse.TopLevelParsed QName, Span)]
  -> Result (Module (HashMap QName (SourceLoc, Unscoped.Definition QName, Unscoped.Type QName)))
resolve modul = case Resolve.modul modul of
  ExceptT (Identity (Left err)) -> Failure $ pure $ ResolveError err
  ExceptT (Identity (Right resolved)) -> Success resolved
