{-# LANGUAGE GeneralizedNewtypeDeriving, MonadComprehensions, OverloadedStrings #-}
module Backend.ExtractExtern where

import Control.Monad.State
import Data.Foldable
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.Monoid
import qualified Data.Text as Text
import Data.Text(Text)
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import Backend.Target
import Syntax
import Syntax.Sized.Anno
import qualified Syntax.Sized.Definition as Sized
import qualified Syntax.Sized.Extracted as Extracted
import qualified Syntax.Sized.Lifted as Lifted
import TypedFreeVar
import qualified TypeRep
import Util
import Util.TopoSort
import Util.Tsil as Tsil
import VIX

-- The idea here is to take blocks of the form
--
-- (C|
--    foo
--    $(a b c)
--    bar
--    $x
--  |)
--
-- and produce a C function taking as argument the free variables of all splices:
--
-- retType f(aType a, bType b, cType c, xType x) {
--    foo
--    f_callback_1(a, b, c);
--    bar
--    x
-- }
--
-- The extern block is replaced with as call to f(a, b, c, x) in the Sixten
-- code.
--
-- We create functions that use the C calling convention for the splices that
-- aren't plain variables, roughly:
--
-- retType' f_callback_1(aType a, bType b, cType c) {
--    [compiled code for 'a b c'];
-- }
--
data ExtractState = ExtractState
  { freshNames :: [QName]
  , extractedCode :: Tsil Text
  , extractedDecls :: Tsil Extracted.Declaration
  , extractedCallbacks :: Tsil (QName, Sized.Function Extracted.Expr Void)
  , target :: Target
  }

newtype Extract a = Extract { unExtract :: StateT ExtractState VIX a }
  deriving (Functor, Applicative, Monad, MonadState ExtractState, MonadVIX, MonadIO)

runExtract :: [QName] -> Target -> Extract a -> VIX ([(QName, Sized.Function Extracted.Expr Void)], Extracted.Submodule a)
runExtract names tgt (Extract m) = do
  (a, s) <- runStateT m (ExtractState names mempty mempty mempty tgt)
  let decls = toList $ extractedDecls s
      defs = toList $ extractedCode s
      cbs = toList $ extractedCallbacks s
  return (cbs, Extracted.Submodule decls ((,) C <$> defs) a)

freshName :: Extract QName
freshName = do
  name:names <- gets freshNames
  modify $ \s -> s { freshNames = names }
  return name

emitDecl :: Extracted.Declaration -> Extract ()
emitDecl d = modify $ \s -> s { extractedDecls = Snoc (extractedDecls s) d }

emitCode :: Text -> Extract ()
emitCode d = modify $ \s -> s { extractedCode = Snoc (extractedCode s) d }

emitCallback
  :: QName
  -> Sized.Function Extracted.Expr Void
  -> Extract ()
emitCallback name fun = modify $ \s -> s { extractedCallbacks = Snoc (extractedCallbacks s) (name, fun) }

type FV = FreeVar Extracted.Expr

extractExpr
  :: Lifted.Expr FV
  -> Extract (Extracted.Expr FV)
extractExpr expr = case expr of
  Lifted.Var v -> return $ Extracted.Var v
  Lifted.Global g -> return $ Extracted.Global g
  Lifted.Lit l -> return $ Extracted.Lit l
  Lifted.Con c es -> Extracted.Con c <$> mapM extractAnnoExpr es
  Lifted.Call e es -> Extracted.Call <$> extractExpr e <*> mapM extractAnnoExpr es
  Lifted.PrimCall retDir e es -> Extracted.PrimCall Nothing retDir
    <$> extractExpr e
    <*> traverse (traverse extractAnnoExpr) es
  Lifted.Let h e s -> do
    e' <- extractAnnoExpr e
    v <- freeVar h $ typeAnno e'
    let body = instantiate1 (pure v) s
    body' <- extractExpr body
    let s' = abstract1 v body'
    return $ Extracted.Let h e' s'
  Lifted.Case e brs -> Extracted.Case <$> extractAnnoExpr e <*> extractBranches brs
  Lifted.ExternCode f typ -> do
    typ' <- extractExpr typ
    f' <- mapM extractAnnoExpr f
    extractExtern typ' f'

extractAnnoExpr
  :: Anno Lifted.Expr FV
  -> Extract (Anno Extracted.Expr FV)
extractAnnoExpr (Anno e t) = Anno <$> extractExpr e <*> extractExpr t

extractExtern
  :: Extracted.Type FV
  -> Extern (Anno Extracted.Expr FV)
  -> Extract (Extracted.Expr FV)
extractExtern retType (Extern C parts) = do
  tgt <- gets target

  let freeVars = foldMap (foldMap $ foldMap HashSet.singleton) parts
      argNames =
        [ (v, "extern_arg_" <> shower n <> fromNameHint mempty (("_" <>) . fromName) (varHint v))
        | (v, n) <- zip (HashSet.toList freeVars) [(0 :: Int)..]
        ]
      typedArgs =
        [ (v, (name, typeStr, dir))
        | (v, name) <- argNames
        , let dir = typeDirection $ varType v
        , let typeStr = externType dir
        ]
      typedArgsMap = HashMap.fromList typedArgs
      argNamesMap = HashMap.fromList argNames

  renderedParts <- forM parts $ \part -> case part of
    ExternPart str -> return str
    TypeMacroPart (Anno typ _) -> return $ externType $ typeDirection typ
    ExprMacroPart (Anno (Extracted.Var v) _) -> return $ argNamesMap HashMap.! v
    ExprMacroPart expr@(Anno _ callbackRetType) -> do
      let callbackFreeVars = toHashSet expr
          callbackParams = toVector $ acyclic <$> topoSortWith id varType callbackFreeVars
      callbackName <- freshName
      let ensureVoid :: FV -> Void
          ensureVoid = error "ExtractExtern: non-void"
          paramsTele = ensureVoid <$> varTelescope ((,) () <$> callbackParams)
          function = Sized.Function paramsTele
            $ ensureVoid
            <$> abstractAnno (teleAbstraction callbackParams) expr
      emitCallback callbackName function
      let callbackArgs = (typedArgsMap HashMap.!) <$> toList callbackFreeVars
          callbackArgNames = fst3 <$> callbackArgs
          callbackArgDirs = toVector $ thd3 <$> callbackArgs
      forwardDeclare callbackName callbackRetType callbackArgDirs

      return
        $ fromName (mangle callbackName)
        <> "("
        <> Text.intercalate ", " callbackArgNames
        <> ")"
    TargetMacroPart PointerAlignment -> return $ shower $ ptrAlign tgt

  name <- mangle <$> freshName

  let retDir = typeDirection retType
      retDir' = toReturnDirection OutParam retDir
      (actualRetTypeStr, retParam) = case retDir' of
        ReturnDirect rep -> (externType (Direct rep), mempty)
        ReturnIndirect Projection -> ("uint8_t*", mempty)
        ReturnIndirect OutParam -> ("void", [externType retDir <> " return_"])
      args = toVector [(dir, Anno (pure var) (varType var)) | (var, (_, _, dir)) <- typedArgs]
      argDirs = fst <$> args
  emitDecl $ Extracted.Declaration name retDir' argDirs
  emitCode
    $ "__attribute__((always_inline))\n"
    <> actualRetTypeStr <> " " <> fromName name
    <> "("
    <> Text.intercalate ", " ([typeStr <> " " <> exprName | (_, (exprName, typeStr, _)) <- typedArgs] <> retParam) <> ") {"
    <> Text.unwords renderedParts
    <> "}"
  return $ Extracted.PrimCall
    (Just C)
    retDir'
    (Extracted.Global $ unqualified name)
    args
  where
    acyclic (AcyclicSCC a) = a
    acyclic (CyclicSCC _) = error "ExtractExtern acyclic"

forwardDeclare
  :: QName
  -> Extracted.Expr FV
  -> Vector Direction
  -> Extract ()
forwardDeclare name retType argDirs = do
  -- TODO out params
  let retDir = typeDirection retType
  emitCode
    $ externType retDir <> " " <> fromName (mangle name)
    <> "("
    <> Text.intercalate ", " (toList $ externType <$> argDirs)
    <> ");"
  addSignatures
    $ HashMap.singleton name
    $ FunctionSig (CompatibleWith C) (toReturnDirection Projection retDir) argDirs

mangle :: QName -> Name
mangle (QName (ModuleName parts) name)
  = Name
  $ Text.intercalate "__" (Vector.toList $ fromName <$> parts)
  <> "__" <> fromName name

typeDirection
  :: Extracted.Expr v
  -> Direction
typeDirection (Extracted.MkType rep) = case TypeRep.size rep of
  0 -> Direct rep
  1 -> Direct rep
  2 -> Direct rep
  4 -> Direct rep
  8 -> Direct rep
  _ -> Indirect
typeDirection _ = Indirect

externType :: Direction -> Text
externType (Direct rep) | TypeRep.size rep == 0 = "void"
externType (Direct rep) = "uint" <> shower (8 * TypeRep.size rep) <> "_t"
externType Indirect = "uint8_t*"

extractBranches
  :: Branches () Lifted.Expr FV
  -> Extract (Branches () Extracted.Expr FV)
extractBranches (ConBranches cbrs) = fmap ConBranches $
  forM cbrs $ \(ConBranch qc tele brScope) -> do
    vs <- forTeleWithPrefixM tele $ \h () s vs -> do
      let e = instantiateTele pure vs s
      e' <- extractExpr e
      freeVar h e'
    let brExpr = instantiateTele pure vs brScope
        abstr = teleAbstraction vs
        tele'' = Telescope $ (\v -> TeleArg (varHint v) () $ abstract abstr $ varType v) <$> vs
    brExpr' <- extractExpr brExpr
    let brScope' = abstract abstr brExpr'
    return $ ConBranch qc tele'' brScope'
extractBranches (LitBranches lbrs def) = LitBranches <$> sequence
  [ LitBranch l <$> extractExpr e
  | LitBranch l e <- lbrs
  ] <*> extractExpr def

extractDef
  :: Target
  -> QName
  -> Sized.Definition Lifted.Expr Void
  -> VIX [(QName, Extracted.Submodule (Sized.Definition Extracted.Expr Void))]
extractDef tgt qname@(QName mname name) def = fmap flatten $ runExtract names tgt $ case def of
  Sized.FunctionDef vis cl (Sized.Function tele scope) ->
    fmap (Sized.FunctionDef vis cl . fmap noFV) $ do
      vs <- forTeleWithPrefixM (vacuous tele) $ \h () s vs -> do
        let e = instantiateTele pure vs s
        e' <- extractExpr e
        freeVar h e'
      let expr = instantiateAnnoTele pure vs $ vacuous scope
          abstr = teleAbstraction vs
          tele'' = Telescope $ (\v -> TeleArg (varHint v) () $ abstract abstr $ varType v) <$> vs
      expr' <- extractAnnoExpr expr
      let scope' = abstractAnno abstr expr'
      return $ Sized.Function tele'' scope'
  Sized.ConstantDef vis (Sized.Constant e) -> Sized.ConstantDef vis . fmap noFV
    <$> (Sized.Constant <$> extractAnnoExpr (vacuous e))
  Sized.AliasDef -> return Sized.AliasDef
  where
    flatten (cbs, def')
      = (qname, def')
      : [ (n, Extracted.emptySubmodule $ Sized.FunctionDef Public Sized.NonClosure f)
        | (n, f) <- cbs
        ]
    noFV :: FV -> Void
    noFV = error "ExtractExtern noFV"
    names =
      [ QName mname $ if n == 0
          then "_extern__" <> name
          else "_extern_" <> shower n <> "__" <> name
      | n <- [(0 :: Int)..]
      ]
