{-# LANGUAGE BangPatterns, GeneralizedNewtypeDeriving, MonadComprehensions, OverloadedStrings #-}
module Backend.ExtractExtern where

import Control.Monad.State
import Data.Foldable
import Data.Monoid
import qualified Data.Text as Text
import Data.Text(Text)
import qualified Data.Vector as Vector

import Backend.Target
import Syntax
import qualified Syntax.Sized.Definition as Sized
import qualified Syntax.Sized.Extracted as Extracted
import qualified Syntax.Sized.Lifted as Lifted
import TypedFreeVar
import qualified TypeRep
import Util
import Util.Tsil as Tsil
import VIX

data ExtractState = ExtractState
  { freshNames :: [QName]
  , extractedCode :: Tsil (Extracted.Declaration, Text)
  , target :: Target
  }

newtype Extract a = Extract { unExtract :: StateT ExtractState VIX a }
  deriving (Functor, Applicative, Monad, MonadState ExtractState, MonadVIX, MonadIO)

runExtract :: [QName] -> Target -> Extract a -> VIX (Extracted.Submodule a)
runExtract names tgt (Extract m) = do
  (a, s) <- runStateT m (ExtractState names mempty tgt)
  let (decls, defs) = unzip $ toList $ extractedCode s
  return $ Extracted.Submodule decls ((,) C <$> defs) a

freshName :: Extract Name
freshName = do
  name:names <- gets freshNames
  modify $ \s -> s { freshNames = names }
  return $ mangle name

addExtractedCode :: Extracted.Declaration -> Text -> Extract ()
addExtractedCode d t = modify $ \s -> s { extractedCode = Snoc (extractedCode s) (d, t) }

type FV = FreeVar Extracted.Expr

extractExpr
  :: Maybe (Extracted.Type FV)
  -> Lifted.Expr FV
  -> Extract (Extracted.Expr FV)
extractExpr mtype expr = case expr of
  Lifted.Var v -> return $ Extracted.Var v
  Lifted.Global g -> return $ Extracted.Global g
  Lifted.Lit l -> return $ Extracted.Lit l
  Lifted.Con c es -> Extracted.Con c <$> mapM (extractExpr Nothing) es
  Lifted.Call e es -> Extracted.Call <$> extractExpr Nothing e <*> mapM (extractExpr Nothing) es
  Lifted.PrimCall retDir e es -> Extracted.PrimCall Nothing retDir
    <$> extractExpr Nothing e
    <*> traverse (traverse (extractExpr Nothing)) es
  Lifted.Let h e t s -> do
    e' <- extractExpr Nothing e
    t' <- extractExpr Nothing t
    v <- freeVar h t'
    let body = instantiate1 (pure v) s
    body' <- extractExpr mtype body
    let s' = abstract1 v body'
    return $ Extracted.Let h e' s'
  Lifted.Case e brs -> Extracted.Case <$> extractExpr Nothing e <*> extractBranches mtype brs
  Lifted.ExternCode f -> case mtype of
    Nothing -> error "extractExpr Nothing"
    Just typ -> extractExtern typ =<< mapM (extractExpr Nothing) f
  Lifted.Anno e t -> do
    t' <- extractExpr Nothing t
    Extracted.Anno <$> extractExpr (Just t') e <*> pure t'

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
-- We create functions that use the C calling convention for the splices that
-- aren't plain variables, roughly:
--
-- retType' f_callback_1(aType a, bType b, cType c) {
--    [compiled code for 'a b c'];
-- }
--
-- Plan:
-- Generate the callback functions and call them
-- Forward-declare callback functions in generated C code
-- Make calling code compile the callback functions
extractExtern
  :: Extracted.Type FV
  -> Extern (Extracted.Expr FV)
  -> Extract (Extracted.Expr FV)
extractExtern retType (Extern C parts) = do
  name <- freshName
  tgt <- gets target
  let (retTypeStr, retDir) = extractType retType
      retDir' = toReturnDirection OutParam retDir
      (actualRetTypeStr, retParam) = case retDir of
        Direct _ -> (retTypeStr, mempty)
        Indirect -> ("void", [retTypeStr <> " return_"])
      (strs, exprs, _) = foldl' (go tgt) (mempty, mempty, 0 :: Int) parts
      exprsList = toList exprs
      funDef
        = "__attribute__((always_inline))\n"
        <> actualRetTypeStr <> " " <> fromName name
        <> "("
        <> Text.intercalate ", " ([typeStr <> " " <> exprName | (_, (exprName, typeStr, _)) <- exprsList] <> retParam) <> ") {"
        <> Text.concat (toList strs)
        <> "}"
      args = toVector [(dir, expr) | (expr, (_, _, dir)) <- exprsList]
      argDirs = fst <$> args
      funDecl = Extracted.Declaration name retDir' argDirs
  addExtractedCode funDecl funDef
  return $ Extracted.PrimCall
    (Just C)
    retDir'
    (Extracted.Global $ unqualified name)
    args
  where
    go tgt (strs, exprs, !len) part = case part of
      ExternPart str -> (Snoc strs str, exprs, len)
      TypeMacroPart typ -> (Snoc strs $ fst (extractType typ) <> " ", exprs, len)
      ExprMacroPart expr@(Extracted.Anno _ typ) ->
        case Tsil.lookup expr exprs of
          Nothing -> (Snoc strs (exprName <> " "), Snoc exprs (expr, (exprName, typeStr, dir)), len + 1)
            where
              (typeStr, dir) = extractType typ
              exprName = "extern_arg_" <> shower len
          Just (exprName, _, _) -> (Snoc strs $ exprName <> " ", exprs, len)
      ExprMacroPart _ -> error "extractExtern"
      TargetMacroPart PointerAlignment -> (Snoc strs $ shower $ ptrAlign tgt, exprs, len)

mangle :: QName -> Name
mangle (QName (ModuleName parts) name)
  = Name
  $ Text.intercalate "__" (Vector.toList $ fromName <$> parts)
  <> "__" <> fromName name

extractType
  :: Extracted.Expr v
  -> (Text, Direction)
extractType (Extracted.MkType rep) = case TypeRep.size rep of
  0 -> ("void", Direct rep)
  1 -> ("uint8_t", Direct rep)
  2 -> ("uint16_t", Direct rep)
  4 -> ("uint32_t", Direct rep)
  8 -> ("uint64_t", Direct rep)
  _ -> ("uint8_t*", Indirect)
extractType _ = ("uint8_t*", Indirect)

extractBranches
  :: Maybe (Extracted.Type FV)
  -> Branches QConstr () Lifted.Expr FV
  -> Extract (Branches QConstr () Extracted.Expr FV)
extractBranches mtype (ConBranches cbrs) = fmap ConBranches $
  forM cbrs $ \(ConBranch qc tele brScope) -> do
    vs <- forTeleWithPrefixM tele $ \h () s vs -> do
      let e = instantiateTele pure vs s
      e' <- extractExpr Nothing e
      freeVar h e'
    let brExpr = instantiateTele pure vs brScope
        abstr = teleAbstraction vs
        tele'' = Telescope $ (\v -> TeleArg (varHint v) () $ abstract abstr $ varType v) <$> vs
    brExpr' <- extractExpr mtype brExpr
    let brScope' = abstract abstr brExpr'
    return $ ConBranch qc tele'' brScope'
extractBranches mtype (LitBranches lbrs def) = LitBranches <$> sequence
  [ LitBranch l <$> extractExpr mtype e
  | LitBranch l e <- lbrs
  ] <*> extractExpr mtype def

extractDef
  :: QName
  -> Sized.Definition Lifted.Expr FV
  -> Target
  -> VIX (Extracted.Submodule (Sized.Definition Extracted.Expr FV))
extractDef (QName mname name) def tgt = runExtract names tgt $ case def of
  Sized.FunctionDef vis cl (Sized.Function tele scope) -> fmap (Sized.FunctionDef vis cl) $ do
    vs <- forTeleWithPrefixM tele $ \h () s vs -> do
      let e = instantiateTele pure vs s
      e' <- extractExpr Nothing e
      freeVar h e'
    let expr = instantiateTele pure vs scope
        abstr = teleAbstraction vs
        tele'' = Telescope $ (\v -> TeleArg (varHint v) () $ abstract abstr $ varType v) <$> vs
    expr' <- extractExpr Nothing expr
    let scope' = abstract abstr expr'
    return $ Sized.Function tele'' scope'
  Sized.ConstantDef vis (Sized.Constant e) -> Sized.ConstantDef vis
    <$> (Sized.Constant <$> extractExpr Nothing e)
  Sized.AliasDef -> return Sized.AliasDef
  where
    names =
      [ QName mname $ if n == 0
          then "_extern__" <> name
          else "_extern_" <> shower n <> "__" <> name
      | n <- [(0 :: Int)..]
      ]
