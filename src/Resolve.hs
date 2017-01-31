{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
-- | Resolving of names
module Resolve where

import Control.Applicative
import Control.Monad.Except
import Data.Hashable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Semigroup
import Data.Text(Text)
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen
import Text.Trifecta.Result(Err(Err), explain)

import Builtin
import Syntax hiding (DataDefinition, Definition)
import Syntax.Concrete.Pattern
import Syntax.Wet as Wet
import Syntax.Parse(TopLevelParsed(..))
import Util

type MaybeTypedDef = (Maybe (Definition Name, Span), Maybe (Expr Name, Span))
type Resolve = (HashMap Name MaybeTypedDef, Maybe Name)

resolveName
  :: Resolve
  -> (TopLevelParsed Name, Span)
  -> Except Text Resolve
resolveName (prog, prevName) (parsedDef, loc) = case parsedDef of
  ParsedClause mName (Wet.Clause pats expr) -> case mName <|> prevName of
    Nothing -> err loc
      "Unresolved wildcard"
      ["Wildcard definitions refer to the first named definition or type declaration above the current line."]
    Just name -> do
      prog' <- insertWithM mergeTypedDef name
        (Just (Definition $ pure $ Wet.Clause pats expr, loc), Nothing)
        prog
      return (prog', Just name)
  ParsedTypeDecl name typ -> do
    prog' <- insertWithM mergeTypedDef name
      (Nothing, Just (typ, loc))
      prog
    return (prog', Just name)
  ParsedData name params dataDef -> do
    let pats = (\(p, n, t) -> (p, AnnoPat t $ VarPat (nameHint n) n)) <$> params
        typ = Wet.pis pats (App (Global Builtin.TypeName) Implicit Wildcard)
        tele = (\(p, n, t) -> (p, n, t)) <$> params
    prog' <- insertWithM mergeTypedDef name
      (Just (DataDefinition tele dataDef, loc), Just (typ, loc))
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
mergeTypedDef (_, Just (_, newLoc)) (Just (DataDefinition _ _, oldLoc), _) = do
  let r = render oldLoc
  err
    newLoc
    "Superfluous type signature"
    [ "Data definitions cannot have free-standing type declarations."
    , "Previous definition at " <> Leijen.pretty (delta r) <> ":"
    , Leijen.pretty r
    ]
mergeTypedDef (_, Just (_, newLoc)) (_, Just (_, oldLoc)) = do
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
mergeDef (Definition newClauses, newLoc) (Definition oldClauses, oldLoc)
  = return (Definition $ oldClauses <> newClauses, addSpan newLoc oldLoc)
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
  $ Err (Just heading) docs mempty

program
  :: [(TopLevelParsed Name, Span)]
  -> Except Text (HashMap Name (SourceLoc, Definition Name, Type Name))
program xs = do
  (prog, _) <- foldM resolveName (mempty, Nothing) xs
  forM prog $ \(mdef, mtyp) -> case (mdef, mtyp) of
    (Nothing, Nothing) -> error "Resolve: The impossible happened"
    (Nothing, Just (_, loc)) -> err loc
      "Type signature without a matching definition"
      []
    (Just (def, defLoc), Just (typ, typLoc)) -> return (render $ addSpan defLoc typLoc, def, typ)
    (Just (def, defLoc), Nothing) -> return (render defLoc, def, Wildcard)
