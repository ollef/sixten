{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Processor.File where

import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.Maybe
import Data.Monoid
import Data.Text(Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Data.Vector as Vector
import Data.Void
import System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen
import qualified Text.Trifecta as Trifecta
import Text.Trifecta.Result(Err(Err), explain)

import Analysis.Denat
import qualified Analysis.ReturnDirection as ReturnDirection
import Analysis.Simplify
import qualified Backend.ClosureConvert as ClosureConvert
import qualified Backend.ExtractExtern as ExtractExtern
import qualified Backend.Generate as Generate
import Backend.Lift
import qualified Backend.SLam as SLam
import Backend.Target
import qualified Frontend.Declassify as Declassify
import qualified Frontend.Parse as Parse
import qualified Frontend.ScopeCheck as ScopeCheck
import qualified Inference.Monad as TypeCheck
import qualified Inference.TypeCheck as TypeCheck
import Processor.Result
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete.Scoped as Concrete
import qualified Syntax.Concrete.Unscoped as Unscoped
import qualified Syntax.Sized.Definition as Sized
import qualified Syntax.Sized.Extracted as Extracted
import qualified Syntax.Sized.Lifted as Lifted
import qualified Syntax.Sized.SLambda as SLambda
import Util
import VIX

-- TODO: Clean this up
type DependencySigs = HashMap QName Text

process
  :: Module (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition))
  -> VIX [Generate.GeneratedSubmodule]
process = frontend backend

frontend
  :: ([(QName, Definition Abstract.Expr Void, Abstract.Expr Void)] -> VIX [k])
  -> Module (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition))
  -> VIX [k]
frontend k
  = scopeCheckProgram
  >>=> prettyConcreteGroup "Concrete syntax" absurd

  >=> declassifyGroup

  >>=> prettyConcreteGroup "Declassified" absurd
  >=> typeCheckGroup

  >=> prettyTypedGroup 9 "Abstract syntax" absurd

  >=> simplifyGroup
  >=> prettyTypedGroup 8 "Simplified" absurd

  >=> addGroupToContext
  >=> k

backend
  :: [(QName, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> VIX [Generate.GeneratedSubmodule]
backend
  = slamGroup
  >=> prettyGroup "SLammed" vac

  >=> denatGroup
  >=> prettyGroup "Denaturalised" vac

  >=> liftGroup
  >>=> prettyGroup "Lambda-lifted" vac

  >=> closureConvertGroup
  >>=> prettyGroup "Closure-converted" vac

  >=> processConvertedGroup
  where
    vac :: Functor e => e Void -> e Name
    vac = vacuous

processConvertedGroup
  :: [(QName, Sized.Definition Lifted.Expr Void)]
  -> VIX [Generate.GeneratedSubmodule]
processConvertedGroup
  = inferGroupDirections
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
  -> [(QName, SourceLoc, Concrete.TopLevelPatDefinition e v, Maybe (e v))]
  -> VIX [(QName, SourceLoc, Concrete.TopLevelPatDefinition e v, Maybe (e v))]
prettyConcreteGroup str f defs = do
  whenVerbose 10 $ do
    VIX.log $ "----- " <> str <> " -----"
    forM_ defs $ \(n, _, d, mt) -> do
      forM_ mt $ \t -> do
        let t' = f <$> t
        VIX.log
          $ showWide
          $ runPrettyM
          $ prettyM n <+> ":" <+> prettyM t'
      VIX.log
        $ showWide
        $ runPrettyM
        $ prettyNamed (prettyM n) (f <$> d)
      VIX.log ""
  return defs

prettyTypedGroup
  :: Int
  -> Text
  -> (v -> QName)
  -> [(QName, Definition Abstract.Expr v, Abstract.Expr v)]
  -> VIX [(QName, Definition Abstract.Expr v, Abstract.Expr v)]
prettyTypedGroup v str f defs = do
  whenVerbose v $ do
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
        $ Abstract.prettyTypedDef (prettyM n) (f <$> d) t'
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
  :: Module (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition))
  -> VIX [[(QName, SourceLoc, Concrete.TopLevelPatDefinition Concrete.Expr Void, Maybe (Concrete.Type Void))]]
scopeCheckProgram m = do
  res <- ScopeCheck.scopeCheckModule m
  let defnames = HashSet.fromMap $ void $ moduleContents m
      connames = HashSet.fromList
        [ QConstr n c
        | (n, (_, Unscoped.TopLevelDataDefinition _ _ d)) <- HashMap.toList $ moduleContents m
        , c <- constrName <$> d
        ]
  addModule (moduleName m) $ HashSet.map Right defnames <> HashSet.map Left connames
  return res

declassifyGroup
  :: [(QName, SourceLoc, Concrete.TopLevelPatDefinition Concrete.Expr Void, Maybe (Concrete.Type Void))]
  -> VIX [[(QName, SourceLoc, Concrete.TopLevelPatDefinition Concrete.Expr Void, Maybe (Concrete.Type Void))]]
declassifyGroup xs = do
  results <- forM xs $
    \(name, loc, def, mtyp) -> Declassify.declassify name loc def mtyp
  let (preResults, postResults) = unzip results
      postResults' = concat postResults
      preResults' = concat preResults
  return $ preResults' : [postResults' | not $ null postResults']

typeCheckGroup
  :: [(QName, SourceLoc, Concrete.TopLevelPatDefinition Concrete.Expr Void, Maybe (Concrete.Expr Void))]
  -> VIX [(QName, Definition Abstract.Expr Void, Abstract.Expr Void)]
typeCheckGroup
  = fmap Vector.toList . TypeCheck.runInfer . TypeCheck.checkTopLevelRecursiveDefs . Vector.fromList

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

liftGroup
  :: [(QName, SLambda.Expr Void)]
  -> VIX [[(QName, Sized.Definition Lifted.Expr Void)]]
liftGroup defs = fmap (Sized.dependencyOrder . concat) $ forM defs $ \(name, e) -> do
  (e', fs) <- liftToDefinition name e
  return $ (name, e') : fmap (second $ Sized.FunctionDef Private Sized.NonClosure) fs

closureConvertGroup
  :: [(QName, Sized.Definition Lifted.Expr Void)]
  -> VIX [[(QName, Sized.Definition Lifted.Expr Void)]]
closureConvertGroup = ClosureConvert.convertDefinitions

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
  target <- getTarget
  return $
    flip map defs $ \(n, d) -> (n, ExtractExtern.extractDef n d target)

generateGroup
  :: [(QName, Extracted.Submodule (Sized.Definition Extracted.Expr Void))]
  -> VIX [Generate.GeneratedSubmodule]
generateGroup defs =
  forM defs $ \(x, m) ->
    Generate.generateSubmodule x $ vacuous <$> m

data ProcessFileArgs = ProcessFileArgs
  { procFile :: FilePath
  , procLlOutput, procCOutput :: FilePath
  , procTarget :: Target
  , procLogHandle :: Handle
  , procVerbosity :: Int
  } deriving (Eq, Show)

writeModule
  :: Module [Generate.GeneratedSubmodule]
  -> FilePath
  -> [(Language, FilePath)]
  -> VIX [(Language, FilePath)]
writeModule modul llOutputFile externOutputFiles = do
  let subModules = moduleContents modul
  Util.withFile llOutputFile WriteMode $
    Generate.writeLlvmModule
      (moduleName modul)
      (moduleImports modul)
      subModules
  liftIO $ fmap catMaybes $
    forM externOutputFiles $ \(lang, outFile) ->
      case fmap snd $ filter ((== lang) . fst) $ concatMap Generate.externs $ moduleContents modul of
        [] -> return Nothing
        externCode -> Util.withFile outFile WriteMode $ \handle -> do
          -- TODO this is C specific
          Text.hPutStrLn handle "#include <stdint.h>"
          Text.hPutStrLn handle "#include <stdio.h>"
          Text.hPutStrLn handle "#include <stdlib.h>"
          Text.hPutStrLn handle "#include <string.h>"
          forM_ externCode $ \code -> do
            Text.hPutStrLn handle ""
            Text.hPutStrLn handle code
          return $ Just (lang, outFile)

parse
  :: FilePath
  -> IO (Result (Module [(SourceLoc, Unscoped.TopLevelDefinition)]))
parse file = do
  parseResult <- Parse.parseFromFileEx Parse.modul file
  case parseResult of
    Trifecta.Failure f -> return $ Failure $ pure $ SyntaxError $ Trifecta._errDoc f
    Trifecta.Success res -> return $ Success res

dupCheck
  :: Module [(SourceLoc, Unscoped.TopLevelDefinition)]
  -> Result (Module (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition)))
dupCheck m = forM m $ flip evalStateT (0 :: Int) . foldM go mempty
  where
    go defs (loc, def) = do
      name <- case def of
        Unscoped.TopLevelDefinition d -> return $ Unscoped.definitionName d
        Unscoped.TopLevelDataDefinition n _ _ -> return n
        Unscoped.TopLevelClassDefinition n _ _ -> return n
        Unscoped.TopLevelInstanceDefinition typ _ -> do
          i <- get
          put $! i + 1
          return $ "instance-" <> shower i <> "-" <> replaceSpaces (shower $ pretty typ)
      let qname = QName (moduleName m) name
      if HashMap.member qname defs then do
        let (prevLoc, _) = defs HashMap.! qname
        lift $ Failure
          $ pure
          $ TypeError
          $ err loc "Duplicate definition"
          [ "Previous definition at " <> Leijen.pretty (delta prevLoc)
          , Leijen.pretty prevLoc
          ]
      else return $ HashMap.insert qname (loc, def) defs
      where
        replaceSpaces (Name n) = Name $ Text.map replaceSpace n
        replaceSpace ' ' = '-'
        replaceSpace c = c

    err :: SourceLoc -> Doc -> [Doc] -> Text
    err loc heading docs
      = shower
      $ explain loc
      $ Err (Just heading) docs mempty mempty
