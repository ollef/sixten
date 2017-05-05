{-# LANGUAGE BangPatterns, GeneralizedNewtypeDeriving, MonadComprehensions, OverloadedStrings #-}
module Backend.ExtractExtern where

import Control.Monad.State
import Data.Bitraversable
import Data.Foldable
import Data.Monoid

import Syntax
import qualified Syntax.Sized.Definition as Sized
import qualified Syntax.Sized.Extracted as Extracted
import qualified Syntax.Sized.Lifted as Lifted
import Util
import Util.Tsil as Tsil

import qualified Data.Text as Text
import Data.Text(Text)

data ExtractState = ExtractState
  { freshNames :: [Name]
  , extractedCode :: Tsil (Extracted.Declaration, Text)
  }

newtype Extract a = Extract { unExtract :: State ExtractState a }
  deriving (Functor, Applicative, Monad, MonadState ExtractState)

runExtract :: [Name] -> Extract a -> Extracted.Module a
runExtract names
  = (\(a, s) -> let (decls, defs) = unzip $ toList $ extractedCode s in
      Extracted.Module decls ((,) C <$> defs) a)
  . flip runState (ExtractState names mempty)
  . unExtract

freshName :: Extract Name
freshName = do
  name:names <- gets freshNames
  modify $ \s -> s { freshNames = names }
  return name

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
    <*> traverse (bitraverse (extractExpr Nothing) pure) es
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
  let (retTypeStr, retDir) = extractType retType
      retDir' = toReturnDirection OutParam retDir
      (actualRetTypeStr, retParam) = case retDir of
        Direct _ -> (retTypeStr, mempty)
        Indirect -> ("void", [retTypeStr <> " return_"])
      (strs, exprs, _) = foldl' go (mempty, mempty, 0 :: Int) parts
      exprsList = toList exprs
      funDef
        = "__attribute__((always_inline))\n"
        <> actualRetTypeStr <> " " <> fromName name
        <> "("
        <> Text.intercalate ", " ([typeStr <> " " <> exprName | (_, (exprName, typeStr, _)) <- exprsList] <> retParam) <> ") {"
        <> Text.concat (toList strs)
        <> "}"
      args = toVector [(expr, dir) | (expr, (_, _, dir)) <- exprsList]
      argDirs = snd <$> args
      funDecl = Extracted.Declaration name retDir' argDirs
  addExtractedCode funDecl funDef
  return $ Extracted.PrimCall
    (Just C)
    retDir'
    (Extracted.Global name)
    args
  where
    go (strs, exprs, !len) part = case part of
      ExternPart str -> (Snoc strs str, exprs, len)
      TypeMacroPart typ -> (Snoc strs $ fst (extractType typ) <> " ", exprs, len)
      ExprMacroPart (Extracted.Anno expr typ) ->
        case Tsil.lookup expr exprs of
          Nothing -> (Snoc strs (exprName <> " "), Snoc exprs (expr, (exprName, typeStr, dir)), len + 1)
            where
              (typeStr, dir) = extractType typ
              exprName = "extern_arg_" <> shower len
          Just (exprName, _, _) -> (Snoc strs $ exprName <> " ", exprs, len)
      ExprMacroPart _ -> error "extractExtern"

extractType
  :: Extracted.Expr v
  -> (Text, Direction)
extractType (Extracted.Lit (Integer 0)) = ("void", Direct 0)
extractType (Extracted.Lit (Integer 1)) = ("uint8_t", Direct 1)
extractType (Extracted.Lit (Integer 2)) = ("uint16_t", Direct 2)
extractType (Extracted.Lit (Integer 4)) = ("uint32_t", Direct 4)
extractType (Extracted.Lit (Integer 8)) = ("uint64_t", Direct 8)
extractType _ = ("uint8_t*", Indirect)

extractBranches
  :: Ord v
  => Branches QConstr () Lifted.Expr v
  -> Extract (Branches QConstr () Extracted.Expr v)
extractBranches (ConBranches cbrs) = ConBranches <$> sequence
  [ (,,) qc <$> extractTelescope tele <*> extractScope s
  | (qc, tele, s) <- cbrs
  ]
extractBranches (LitBranches lbrs def) = LitBranches <$> sequence
  [ (,) l <$> extractExpr Nothing e
  | (l, e) <- lbrs
  ] <*> extractExpr Nothing def

extractTelescope
  :: Ord v
  => Telescope d Lifted.Expr v
  -> Extract (Telescope d Extracted.Expr v)
extractTelescope (Telescope tele) = Telescope
  <$> mapM (\(h, d, s) -> (,,) h d <$> extractScope s) tele

extractScope
  :: (Ord b, Ord v)
  => Scope b Lifted.Expr v
  -> Extract (Scope b Extracted.Expr v)
extractScope = fmap toScope . extractExpr Nothing . fromScope

extractDef
  :: Ord v
  => Name
  -> Sized.Definition Lifted.Expr v
  -> Extracted.Module (Sized.Definition Extracted.Expr v)
extractDef name def = case def of
  Sized.FunctionDef vis cl (Sized.Function tele s) -> runExtract names
    $ Sized.FunctionDef vis cl
    <$> (Sized.Function <$> extractTelescope tele <*> extractScope s)
  Sized.ConstantDef vis (Sized.Constant e) -> runExtract names
    $ Sized.ConstantDef vis
    <$> (Sized.Constant <$> extractExpr Nothing e)
  where
    names =
      [ if n == 0
          then "sixten_extern__" <> name
          else "sixten_extern_" <> shower n <> "__" <> name
      | n <- [(0 :: Int)..]
      ]

moduleExterns :: Language -> [Extracted.Module innards] -> [Text]
moduleExterns lang modules = do
  modul <- modules
  (lang', code) <- Extracted.moduleExterns modul
  guard $ lang == lang'
  return code
