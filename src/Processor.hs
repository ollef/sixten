{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Processor where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
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

import qualified Builtin
import Close
import ClosureConvert
import qualified Dry
import Erase
import qualified Generate
import qualified Infer
import qualified InferDirection
import qualified InferErasability
import Lift
import qualified LLVM
import Paths_sixten
import qualified Resolve
import Simplify
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Closed as Closed
import qualified Syntax.Concrete as Concrete
import qualified Syntax.Converted as Converted
import qualified Syntax.Lifted as Lifted
import qualified Syntax.Parse as Parse
import qualified Syntax.SLambda as SLambda
import qualified Syntax.Wet as Wet
import Target
import TCM
import Util

processResolved
  :: HashMap Name (SourceLoc, Wet.Definition Name, Wet.Type Name)
  -> TCM [(LLVM.B, LLVM.B)]
processResolved
  = pure . Dry.dryProgram
  >>=> processGroup

processGroup
  :: [(Name, SourceLoc, Concrete.PatDefinition Concrete.Expr Void, Concrete.Expr Void)]
  -> TCM [(LLVM.B, LLVM.B)]
processGroup
  = {- prettyLocatedGroup "Concrete syntax" id -- TODO
  >=> -} typeCheckGroup
  >=> prettyTypedGroup "Abstract syntax" absurd
  >=> simplifyGroup
  >=> prettyTypedGroup "Simplified" absurd
  >=> processAbstractGroup

processAbstractGroup
  :: [(Name, Definition Abstract.ExprP Void, Abstract.ExprP Void)]
  -> TCM [(LLVM.B, LLVM.B)]
processAbstractGroup
  = addGroupToContext
  >=> inferGroupErasability
  >=> prettyTypedGroup "Inferred erasability" absurd
  >=> simplifyGroup
  >=> prettyTypedGroup "Simplified again" absurd
  >=> addErasableGroupToContext
  >=> eraseGroup
  >=> prettyGroup "Erased (SLambda)" absurd
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

prettyLocatedGroup
  :: (Pretty (e Name), Functor e, Eq1 e, Syntax e, Eq (Annotation e), PrettyAnnotation (Annotation e))
  => Text
  -> (v -> Name)
  -> [(Name, x, Definition e v, e v)]
  -> TCM [(Name, x, Definition e v, e v)]
prettyLocatedGroup x f defs = do
  void $ prettyTypedGroup x f $ (\(n, _, d, t) -> (n, d, t)) <$> defs
  return defs

prettyTypedGroup
  :: (Pretty (e Name), Functor e, Eq1 e, Syntax e, Eq (Annotation e), PrettyAnnotation (Annotation e))
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
  -> TCM [(Name, Definition Abstract.ExprP Void, Abstract.ExprP Void)]
typeCheckGroup = fmap Vector.toList . Infer.checkRecursiveDefs . Vector.fromList

simplifyGroup
  :: Eq a
  => [(Name, Definition (Abstract.Expr a) Void, Abstract.Expr a Void)]
  -> TCM [(Name, Definition (Abstract.Expr a) Void, Abstract.Expr a Void)]
simplifyGroup defs = forM defs $ \(x, def, typ) ->
  return (x, simplifyDef def, simplifyExpr False typ)

addGroupToContext
  :: [(Name, Definition Abstract.ExprP Void, Abstract.ExprP Void)]
  -> TCM [(Name, Definition Abstract.ExprP Void, Abstract.ExprP Void)]
addGroupToContext defs = do
  addContext $ HashMap.fromList $ (\(n, d, t) -> (n, (d, t))) <$> defs
  return defs

inferGroupErasability
  :: PrettyAnnotation a
  => [(Name, Definition (Abstract.Expr a) Void, Abstract.Expr a Void)]
  -> TCM [(Name, Definition Abstract.ExprE Void, Abstract.ExprE Void)]
inferGroupErasability defs = do
  let names = Vector.fromList [n | (n, _, _) <- defs]
      glob n = maybe (global n) (pure . B) $ Vector.elemIndex n names
      exposedDefs = Vector.fromList
        [ ( n
          , bound absurd glob d
          , toScope $ bind absurd glob t
          )
        | (n, d, t) <- defs]
  inferredDefs <- InferErasability.inferRecursiveDefs exposedDefs

  let vf :: InferErasability.MetaVar -> TCM b
      vf v = throwError $ "inferGroupErasability " ++ show v
  inferredDefs' <- traverse (bitraverse (traverse $ traverse vf) (traverse vf)) inferredDefs
  let instDefs =
        [ ( names Vector.! i
          , instantiateDef (global . (names Vector.!)) d
          , instantiate (global . (names Vector.!)) t
          )
        | (i, (d, t)) <- zip [0..] $ Vector.toList inferredDefs'
        ]
  return instDefs

addErasableGroupToContext
  :: [(Name, Definition Abstract.ExprE Void, Abstract.ExprE Void)]
  -> TCM [(Name, Definition Abstract.ExprE Void, Abstract.ExprE Void)]
addErasableGroupToContext defs = do
  addErasableContext $ HashMap.fromList $ (\(n, d, t) -> (n, (d, t))) <$> defs
  return defs

eraseGroup
  :: [(Name, Definition Abstract.ExprE Void, Abstract.ExprE Void)] 
  -> TCM [(Name, SLambda.Expr Void)]
eraseGroup defs = sequence
  [ do
      d' <- eraseDef (vacuous d) (vacuous t)
      d'' <- traverse (throwError . ("eraseGroup " ++) . show) d'
      return (x, d'')
  | (x, d, t) <- defs
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
  addConvertedSignatures $ HashMap.fromList $ fmap fakeSignature <$> fs
  return $ (name, e') : fmap (second $ Lifted.FunctionDef Private) fs
  where
    -- TODO this isn't a very nice way to do this
    fakeSignature
      :: Lifted.Function ClosureDir (Lifted.Expr ClosureDir) Void
      -> Converted.Signature Converted.Expr Unit Void
    fakeSignature (Lifted.Function retDir tele _body)
      = Converted.Function
        retDir
        (Telescope $ (\(h, d) -> (h, d, Scope $ Converted.Lit 0)) <$> tele)
        $ Scope Unit

inferGroupDirections
  :: [(Name, Lifted.Definition ClosureDir (Lifted.Expr ClosureDir) Void)]
  -> TCM [(Name, Lifted.Definition RetDir (Lifted.Expr RetDir) Void)]
inferGroupDirections defs = do
  let names = Vector.fromList $ fst <$> defs
      glob n = maybe (global n) (pure . B) $ Vector.elemIndex n names
      exposedDefs = Vector.fromList
        [ ( n
          , bound absurd glob d
          )
        | (n, d) <- defs]
  inferredDefs <- InferDirection.inferRecursiveDefs exposedDefs

  let vf :: InferDirection.MetaVar -> TCM b
      vf v = throwError $ "inferGroupDirections " ++ show v
  inferredDefs' <- traverse (traverse $ traverse vf) inferredDefs
  let instDefs =
        [ ( names Vector.! i
          , Lifted.instantiateDef (global . (names Vector.!)) d
          )
        | (i, d) <- zip [0..] $ Vector.toList inferredDefs'
        ]
  return instDefs

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
      addContext Builtin.contextP
      addErasableContext Builtin.contextE
      addConvertedSignatures $ Converted.signature <$> Builtin.convertedContext
      builtins <- processConvertedGroup $ HashMap.toList Builtin.convertedContext
      results <- processResolved resolved
      return $ builtins ++ results
