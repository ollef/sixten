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
import qualified TypeRep
import Util
import Util.Tsil as Tsil

data ExtractState = ExtractState
  { freshNames :: [QName]
  , extractedCode :: Tsil (Extracted.Declaration, Text)
  , target :: Target
  }

newtype Extract a = Extract { unExtract :: State ExtractState a }
  deriving (Functor, Applicative, Monad, MonadState ExtractState)

runExtract :: [QName] -> Target -> Extract a -> Extracted.Submodule a
runExtract names tgt
  = (\(a, s) -> let (decls, defs) = unzip $ toList $ extractedCode s in
      Extracted.Submodule decls ((,) C <$> defs) a)
  . flip runState (ExtractState names mempty tgt)
  . unExtract

freshName :: Extract Name
freshName = do
  name:names <- gets freshNames
  modify $ \s -> s { freshNames = names }
  return $ mangle name

addExtractedCode :: Extracted.Declaration -> Text -> Extract ()
addExtractedCode d t = modify $ \s -> s { extractedCode = Snoc (extractedCode s) (d, t) }

extractExpr
  :: Ord v
  => Maybe (Extracted.Type v)
  -> Lifted.Expr v
  -> Extract (Extracted.Expr v)
extractExpr mtype expr = case expr of
  Lifted.Var v -> return $ Extracted.Var v
  Lifted.Global g -> return $ Extracted.Global g
  Lifted.Lit l -> return $ Extracted.Lit l
  Lifted.Con c es -> Extracted.Con c <$> mapM (extractExpr Nothing) es
  Lifted.Call e es -> Extracted.Call <$> extractExpr Nothing e <*> mapM (extractExpr Nothing) es
  Lifted.PrimCall retDir e es -> Extracted.PrimCall Nothing retDir
    <$> extractExpr Nothing e
    <*> traverse (traverse (extractExpr Nothing)) es
  Lifted.Let h e s -> Extracted.Let h
    <$> extractExpr Nothing e
    <*> extractScope s
  Lifted.Case e brs -> Extracted.Case <$> extractExpr Nothing e <*> extractBranches brs
  Lifted.ExternCode f -> case mtype of
    Nothing -> error "extractExpr Nothing"
    Just typ -> extractExtern typ =<< mapM (extractExpr Nothing) f
  Lifted.Anno e t -> do
    t' <- extractExpr Nothing t
    Extracted.Anno <$> extractExpr (Just t') e <*> pure t'

extractExtern
  :: Ord v
  => Extracted.Type v
  -> Extern (Extracted.Expr v)
  -> Extract (Extracted.Expr v)
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
  :: Ord v
  => Branches QConstr () Lifted.Expr v
  -> Extract (Branches QConstr () Extracted.Expr v)
extractBranches (ConBranches cbrs) = ConBranches <$> sequence
  [ ConBranch qc <$> extractTelescope tele <*> extractScope s
  | ConBranch qc tele s <- cbrs
  ]
extractBranches (LitBranches lbrs def) = LitBranches <$> sequence
  [ LitBranch l <$> extractExpr Nothing e
  | LitBranch l e <- lbrs
  ] <*> extractExpr Nothing def

extractTelescope
  :: Ord v
  => Telescope d Lifted.Expr v
  -> Extract (Telescope d Extracted.Expr v)
extractTelescope (Telescope tele) = Telescope
  <$> mapM (\(TeleArg h d s) -> TeleArg h d <$> extractScope s) tele

extractScope
  :: (Ord b, Ord v)
  => Scope b Lifted.Expr v
  -> Extract (Scope b Extracted.Expr v)
extractScope = fmap toScope . extractExpr Nothing . fromScope

extractDef
  :: Ord v
  => QName
  -> Sized.Definition Lifted.Expr v
  -> Target
  -> Extracted.Submodule (Sized.Definition Extracted.Expr v)
extractDef (QName mname name) def tgt = case def of
  Sized.FunctionDef vis cl (Sized.Function tele s) -> runExtract names tgt
    $ Sized.FunctionDef vis cl
    <$> (Sized.Function <$> extractTelescope tele <*> extractScope s)
  Sized.ConstantDef vis (Sized.Constant e) -> runExtract names tgt
    $ Sized.ConstantDef vis
    <$> (Sized.Constant <$> extractExpr Nothing e)
  Sized.AliasDef -> runExtract names tgt $ return Sized.AliasDef
  where
    names =
      [ QName mname $ if n == 0
          then "_extern__" <> name
          else "_extern_" <> shower n <> "__" <> name
      | n <- [(0 :: Int)..]
      ]
