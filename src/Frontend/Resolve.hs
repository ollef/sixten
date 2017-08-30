{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
-- | Resolving of names
module Frontend.Resolve where

import Control.Applicative
import Control.Monad.Except
import Data.Hashable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Semigroup
import Data.Text(Text)
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen
import Text.Trifecta.Result(Err(Err), explain)

import qualified Builtin.Names as Builtin
import Syntax hiding (DataDefinition, Definition)
import Syntax.Concrete.Pattern
import Syntax.Concrete.Unscoped as Unscoped
import Frontend.Parse(TopLevelParsed(..))
import Util

type MaybeTypedDef = (Maybe (Definition QName, Span), Maybe (Abstract, Type QName, Span))
type Resolve = (HashMap QName MaybeTypedDef, Maybe Name)

resolveName
  :: ModuleName
  -> Resolve
  -> (TopLevelParsed QName, Span)
  -> Except Text Resolve
resolveName modName (prog, prevName) (parsedDef, loc) = case parsedDef of
  ParsedClause mName (Unscoped.Clause pats expr) -> case mName <|> prevName of
    Nothing -> err loc
      "Unresolved wildcard"
      ["Wildcard definitions refer to the first named definition or type declaration above the current line."]
    Just name -> do
      prog' <- insertWithM mergeTypedDef (QName modName name)
        (Just (Definition Concrete $ pure $ Unscoped.Clause pats expr, loc), Nothing)
        prog
      return (prog', Just name)
  ParsedTypeDecl a name typ -> do
    prog' <- insertWithM mergeTypedDef (QName modName name)
      (Nothing, Just (a, typ, loc))
      prog
    return (prog', Just name)
  ParsedData name params dataDef -> do
    let pats = (\(p, n, t) -> (p, AnnoPat t $ VarPat (nameHint n) $ unqualified n)) <$> params
        typ = Unscoped.pis pats (Var Builtin.TypeName)
        tele = (\(p, n, t) -> (p, n, t)) <$> params
    prog' <- insertWithM mergeTypedDef (QName modName name)
      (Just (DataDefinition tele dataDef, loc), Just (Concrete, typ, loc))
      prog
    return (prog', Nothing)

mergeTypedDef
  :: MaybeTypedDef
  -> MaybeTypedDef
  -> Except Text MaybeTypedDef
mergeTypedDef (Nothing, Nothing) old = return old
mergeTypedDef new (Nothing, Nothing) = return new
mergeTypedDef (Nothing, mnewType) (moldDef, Nothing) = return (moldDef, mnewType)
mergeTypedDef (mnewDef, Nothing) (Nothing, moldType) = return (mnewDef, moldType)
mergeTypedDef (Just newDef, mnewType) (Just oldDef, Nothing) = do
  d <- mergeDef newDef oldDef
  return (Just d, mnewType)
mergeTypedDef (Just newDef, Nothing) (Just oldDef, moldType) = do
  d <- mergeDef newDef oldDef
  return (Just d, moldType)
mergeTypedDef (_, Just (_, _, newLoc)) (Just (DataDefinition _ _, oldLoc), _) = do
  let r = render oldLoc
  err
    newLoc
    "Superfluous type signature"
    [ "Data definitions cannot have free-standing type declarations."
    , "Previous definition at " <> Leijen.pretty (delta r) <> ":"
    , Leijen.pretty r
    ]
mergeTypedDef (_, Just (_, _, newLoc)) (_, Just (_, _, oldLoc)) = do
  let r = render oldLoc
  err
    newLoc
    "Duplicate type signature"
    [ "Previous signature at " <> Leijen.pretty (delta r) <> ":"
    , Leijen.pretty r
    ]

mergeDef
  :: (Definition v, Span)
  -> (Definition v, Span)
  -> Except Text (Definition v, Span)
mergeDef (Definition newA newClauses, newLoc) (Definition oldA oldClauses, oldLoc)
  = return (Definition (min newA oldA) $ oldClauses <> newClauses, addSpan newLoc oldLoc)
mergeDef (_, newLoc) (_, oldLoc) = do
  let r = render oldLoc
  err
    newLoc
    "Duplicate definition"
    [ "Previous definition at " <> Leijen.pretty (delta r) <> ":"
    , Leijen.pretty r
    ]

insertWithM
  :: (Eq k, Hashable k, Monad m)
  => (v -> v -> m v) -> k -> v -> HashMap k v -> m (HashMap k v)
insertWithM f k new m = case HashMap.lookup k m of
  Just old -> do
    new' <- f new old
    return $ HashMap.insert k new' m
  Nothing -> return $ HashMap.insert k new m

err :: MonadError Text m => Span -> Doc -> [Doc] -> m a
err loc heading docs
  = throwError
  $ shower
  $ explain (render loc)
  $ Err (Just heading) docs mempty mempty

program
  :: ModuleName
  -> [(TopLevelParsed QName, Span)]
  -> Except Text (HashMap QName (SourceLoc, Definition QName, Type QName))
program modName xs = do
  (prog, _) <- foldM (resolveName modName) (mempty, Nothing) xs
  forM prog $ \(mdef, mtyp) -> case (mdef, mtyp) of
    (Nothing, Nothing) -> error "Resolve: The impossible happened"
    (Nothing, Just (_, _, loc)) -> err loc
      "Type signature without a matching definition"
      []
    (Just (def, defLoc), Just (a, typ, typLoc)) -> return (render $ addSpan defLoc typLoc, withAbstract a def, typ)
    (Just (def, defLoc), Nothing) -> return (render defLoc, def, Wildcard)

withAbstract :: Abstract -> Definition v -> Definition v
withAbstract a (Definition a' e) = Definition (min a a') e
withAbstract _ d@DataDefinition {} = d

modul
  :: Module [(TopLevelParsed QName, Span)]
  -> Except Text (Module (HashMap QName (SourceLoc, Definition QName, Type QName)))
modul m = do
  newContents <- program (moduleName m) $ moduleContents m
  return m
    { moduleImports = Import "Sixten.Builtin" "Sixten.Builtin" AllExposed : moduleImports m
    , moduleContents = newContents
    }
