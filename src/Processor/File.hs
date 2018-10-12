{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TupleSections, OverloadedStrings #-}
module Processor.File where

import Protolude hiding (moduleName, TypeError, handle)

import Data.Char
import Data.Functor.Classes
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.Text(Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector
import Error

import Analysis.Cycle
import Analysis.Denat
import qualified Analysis.ReturnDirection as ReturnDirection
import Analysis.Simplify
import qualified Backend.ClosureConvert as ClosureConvert
import qualified Backend.ExtractExtern as ExtractExtern
import qualified Backend.Generate as Generate
import Backend.Lift
import qualified Backend.SLam as SLam
import Backend.Target
import qualified Elaboration.Monad as TypeCheck
import qualified Elaboration.TypeCheck.Definition as TypeCheck
import qualified Frontend.ResolveNames as ResolveNames
import MonadLog
import Processor.Result
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Pre.Scoped as Pre
import qualified Syntax.Pre.Unscoped as Unscoped
import Syntax.Sized.Anno
import qualified Syntax.Sized.Definition as Sized
import qualified Syntax.Sized.Extracted as Extracted
import qualified Syntax.Sized.Lifted as Lifted
import qualified Syntax.Sized.SLambda as SLambda
import Util
import VIX

process
  :: (ModuleHeader, HashMap QName (SourceLoc, Unscoped.TopLevelDefinition))
  -> VIX [Generate.GeneratedSubmodule]
process = frontend backend

frontend
  :: ([(QName, SourceLoc, ClosedDefinition Core.Expr, Biclosed Core.Expr)] -> VIX [k])
  -> (ModuleHeader, HashMap QName (SourceLoc, Unscoped.TopLevelDefinition))
  -> VIX [k]
frontend k
  = resolveProgramNames
  >>=> prettyPreGroup "Pre-syntax"

  >=> typeCheckGroup

  >=> prettyTypedGroup 9 "Core syntax"

  >=> cycleCheckGroup

  >=> simplifyGroup
  >=> prettyTypedGroup 8 "Simplified"

  >=> addGroupToEnvironment
  >=> k

backend
  :: [(QName, SourceLoc, ClosedDefinition Core.Expr, Biclosed Core.Expr)]
  -> VIX [Generate.GeneratedSubmodule]
backend
  = slamGroup
  >=> prettyGroup "SLammed"

  >=> denatGroup
  >=> prettyGroup "Denaturalised"

  >=> liftGroup
  >>=> prettyGroup "Lambda-lifted"

  >=> closureConvertGroup
  >>=> prettyGroup "Closure-converted"

  >=> processConvertedGroup

processConvertedGroup
  :: [(QName, Closed (Sized.Definition Lifted.Expr))]
  -> VIX [Generate.GeneratedSubmodule]
processConvertedGroup
  = inferGroupDirections
  >=> addSignaturesToEnvironment
  >=> prettyGroup "Directed (lifted)"

  >=> extractExternGroup
  -- TODO
  -- >=> prettyGroup "Extern extracted"

  >=> generateGroup

infixr 1 >>=>
(>>=>) :: Monad m => (a -> m [b]) -> (b -> m [c]) -> a -> m [c]
(f >>=> g) a = concat <$> (f a >>= mapM g)

prettyPreGroup
  :: (Pretty (e Doc), Monad e, Eq1 e)
  => Text
  -> [(QName, SourceLoc, Closed (Pre.Definition e))]
  -> VIX [(QName, SourceLoc, Closed (Pre.Definition e))]
prettyPreGroup str defs = do
  whenVerbose 10 $ do
    MonadLog.log $ "----- " <> str <> " -----"
    forM_ defs $ \(n, _, Closed d) -> do
      MonadLog.log
        $ showWide
        $ pretty
        $ prettyNamed (prettyM n) d
      MonadLog.log ""
  return defs

prettyTypedGroup
  :: Int
  -> Text
  -> [(QName, SourceLoc, ClosedDefinition Core.Expr, Biclosed Core.Expr)]
  -> VIX [(QName, SourceLoc, ClosedDefinition Core.Expr, Biclosed Core.Expr)]
prettyTypedGroup v str defs = do
  whenVerbose v $ do
    MonadLog.log $ "----- " <> str <> " -----"
    forM_ defs $ \(n, _, ClosedDefinition d, Biclosed t) -> do
      MonadLog.log
        $ showWide
        $ pretty
        $ prettyM n <+> ":" <+> prettyM (t :: Core.Expr Void Doc)
      MonadLog.log
        $ showWide
        $ pretty
        $ prettyNamed (prettyM n) (d :: Definition (Core.Expr Void) Doc)
      MonadLog.log ""
  return defs

prettyGroup
  :: forall e. Pretty (e Doc)
  => Text
  -> [(QName, Closed e)]
  -> VIX [(QName, Closed e)]
prettyGroup str defs = do
  whenVerbose 10 $ do
    MonadLog.log $ "----- " <> str <> " -----"
    forM_ defs $ \(n, Closed d) -> do
      MonadLog.log
        $ showWide
        $ pretty
        $ prettyM n <+> "=" <+> prettyM (d :: e Doc)
      MonadLog.log ""
  return defs

resolveProgramNames
  :: (ModuleHeader, HashMap QName (SourceLoc, Unscoped.TopLevelDefinition))
  -> VIX [[(QName, SourceLoc, Closed (Pre.Definition Pre.Expr))]]
resolveProgramNames (moduleHeader, defs) = do
  res <- ResolveNames.resolveModule moduleHeader defs
  let defnames = HashSet.fromMap $ void defs
      connames = HashSet.fromList
        [ QConstr n c
        | (n, (_, Unscoped.TopLevelDataDefinition _ _ cs)) <- HashMap.toList defs
        , c <- constrName <$> cs
        ]
      methods = HashSet.fromList
        [ QName n m
        | (QName n _, (_, Unscoped.TopLevelClassDefinition _ _ ms)) <- HashMap.toList defs
        , m <- methodName <$> ms
        ]
  addModule (moduleName moduleHeader) connames $ defnames <> methods
  return res

typeCheckGroup
  :: [(QName, SourceLoc, Closed (Pre.Definition Pre.Expr))]
  -> VIX [(QName, SourceLoc, ClosedDefinition Core.Expr, Biclosed Core.Expr)]
typeCheckGroup
  = fmap Vector.toList . TypeCheck.runElaborate . TypeCheck.checkAndGeneraliseTopLevelDefs . Vector.fromList

cycleCheckGroup
  :: [(QName, SourceLoc, ClosedDefinition Core.Expr, Biclosed Core.Expr)]
  -> VIX [(QName, SourceLoc, ClosedDefinition Core.Expr, Biclosed Core.Expr)]
cycleCheckGroup defs = do
  defs' <- cycleCheck [(x, loc, def, typ) | (x, loc, ClosedDefinition def, Biclosed typ) <- defs]
  return $ do
    (x, loc, def, typ) <- defs'
    return
      ( x
      , loc
      , closeDefinition identity (panic "cycleCheckGroup close def") def
      , biclose identity (panic "cycleCheckGroup close typ") typ
      )

simplifyGroup
  :: [(QName, SourceLoc, ClosedDefinition Core.Expr, Biclosed Core.Expr)]
  -> VIX [(QName, SourceLoc, ClosedDefinition Core.Expr, Biclosed Core.Expr)]
simplifyGroup defs = return $ do
  (x, loc, ClosedDefinition def, Biclosed typ) <- defs
  return (x, loc, closeDefinition identity identity $ simplifyDef globTerm def, biclose identity identity $ simplifyExpr globTerm 0 typ)
  where
    globTerm x = not $ HashSet.member x names
    names = HashSet.fromList $ (\(x, _, _, _) -> x) <$> defs

addGroupToEnvironment
  :: [(QName, SourceLoc, ClosedDefinition Core.Expr, Biclosed Core.Expr)]
  -> VIX [(QName, SourceLoc, ClosedDefinition Core.Expr, Biclosed Core.Expr)]
addGroupToEnvironment defs = do
  addEnvironment $ HashMap.fromList $ (\(n, loc, d, t) -> (n, (loc, d, t))) <$> defs
  return defs

slamGroup
  :: [(QName, SourceLoc, ClosedDefinition Core.Expr, Biclosed Core.Expr)]
  -> VIX [(QName, Closed (Anno SLambda.Expr))]
slamGroup defs = forM defs $ \(x, _, ClosedDefinition d, _t) -> do
  d' <- SLam.runSlam $ SLam.slamDef d
  return (x, close (panic "slamGroup") d')

denatGroup
  :: [(QName, Closed (Anno SLambda.Expr))]
  -> VIX [(QName, Closed (Anno SLambda.Expr))]
denatGroup defs = return [(n, close identity $ denatAnno def) | (n, Closed def) <- defs]

liftGroup
  :: [(QName, Closed (Anno SLambda.Expr))]
  -> VIX [[(QName, Closed (Sized.Definition Lifted.Expr))]]
liftGroup defs = fmap (Sized.dependencyOrder . concat) $ forM defs $ \(name, e) -> do
  (e', fs) <- liftToDefinition name e
  return $ (name, e') : fmap (second $ mapClosed $ Sized.FunctionDef Private Sized.NonClosure) fs

closureConvertGroup
  :: [(QName, Closed (Sized.Definition Lifted.Expr))]
  -> VIX [[(QName, Closed (Sized.Definition Lifted.Expr))]]
closureConvertGroup = ClosureConvert.convertDefinitions

inferGroupDirections
  :: [(QName, Closed (Sized.Definition Lifted.Expr))]
  -> VIX [(QName, Closed (Sized.Definition Lifted.Expr), Signature ReturnIndirect)]
inferGroupDirections
  = fmap Vector.toList . ReturnDirection.inferRecursiveDefs . Vector.fromList

addSignaturesToEnvironment
  :: [(QName, Closed (Sized.Definition Lifted.Expr), Signature ReturnIndirect)]
  -> VIX [(QName, Closed (Sized.Definition Lifted.Expr))]
addSignaturesToEnvironment defs = do
  let sigs = HashMap.fromList [(n, sig) | (n, _, sig) <- defs]
  logShow 11 "signatures" sigs
  addSignatures sigs
  return [(n, def) | (n, def, _) <- defs]

extractExternGroup
  :: [(QName, Closed (Sized.Definition Lifted.Expr))]
  -> VIX [(QName, Extracted.Submodule (Closed (Sized.Definition Extracted.Expr)))]
extractExternGroup defs = do
  target <- getTarget
  concat <$> forM defs (uncurry $ ExtractExtern.extractDef target)

generateGroup
  :: [(QName, Extracted.Submodule (Closed (Sized.Definition Extracted.Expr)))]
  -> VIX [Generate.GeneratedSubmodule]
generateGroup defs =
  forM defs $ uncurry Generate.generateSubmodule

data ProcessFileArgs = ProcessFileArgs
  { procFile :: FilePath
  , procLlOutput, procCOutput :: FilePath
  , procTarget :: Target
  , procLogHandle :: Handle
  , procVerbosity :: Int
  } deriving (Eq, Show)

writeModule
  :: ModuleHeader
  -> [Generate.GeneratedSubmodule]
  -> FilePath
  -> [(Language, FilePath)]
  -> VIX [(Language, FilePath)]
writeModule moduleHeader subModules llOutputFile externOutputFiles = do
  Util.withFile llOutputFile WriteMode $
    Generate.writeLlvmModule
      (moduleName moduleHeader)
      (moduleImports moduleHeader)
      subModules
  liftIO $ fmap catMaybes $
    forM externOutputFiles $ \(lang, outFile) ->
      case fmap snd $ filter ((== lang) . fst) $ concatMap Generate.externs subModules of
        [] -> return Nothing
        externCode -> Util.withFile outFile WriteMode $ \handle -> do
          -- TODO this is C specific
          Text.hPutStrLn handle "#include <inttypes.h>"
          Text.hPutStrLn handle "#include <stdint.h>"
          Text.hPutStrLn handle "#include <stdio.h>"
          Text.hPutStrLn handle "#include <stdlib.h>"
          Text.hPutStrLn handle "#include <string.h>"
          Text.hPutStrLn handle "#ifdef _WIN32"
          Text.hPutStrLn handle "#include <io.h>"
          Text.hPutStrLn handle "#else"
          Text.hPutStrLn handle "#include <unistd.h>"
          Text.hPutStrLn handle "#endif"
          forM_ externCode $ \code -> do
            Text.hPutStrLn handle ""
            Text.hPutStrLn handle code
          return $ Just (lang, outFile)

dupCheck
  :: ModuleHeader
  -> [(SourceLoc, Unscoped.TopLevelDefinition)]
  -> Result (ModuleHeader, HashMap QName (SourceLoc, Unscoped.TopLevelDefinition))
dupCheck m = fmap (m,) . flip evalStateT (0 :: Int) . foldM go mempty
  where
    go defs (loc, def) = do
      name <- case def of
        Unscoped.TopLevelDefinition d -> return $ Unscoped.definitionName d
        Unscoped.TopLevelDataDefinition n _ _ -> return n
        Unscoped.TopLevelClassDefinition n _ _ -> return n
        Unscoped.TopLevelInstanceDefinition typ _ -> do
          i <- get
          put $! i + 1
          return $ "instance-" <> shower i <> instanceNameEnding (shower $ pretty typ)
      let qname = QName (moduleName m) name
      if HashMap.member qname defs then do
        let (prevLoc, _) = defs HashMap.! qname
        lift $ Failure
          $ pure
          $ TypeError
            "Duplicate definition"
            (Just loc)
            $ PP.vcat
              [ "Previous definition at " <> pretty prevLoc
              , pretty prevLoc
              ]
      else return $ HashMap.insert qname (loc, def) defs
      where
        instanceNameEnding n
          | Text.all (\b -> isAlphaNum b || isSpace b) n = fromText $ "-" <> Text.map replaceSpace n
          | otherwise = ""
        replaceSpace ' ' = '-'
        replaceSpace c = c
