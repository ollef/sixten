{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
-- | Resolving of names
module Resolve where

import Control.Applicative
import Control.Monad.Except
import Data.Hashable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HM
import Data.Monoid
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
  ParsedDefLine mName (Wet.DefLine pats expr) -> case mName <|> prevName of
    Nothing -> err loc
      "Unresolved wildcard"
      ["Wildcard definitions refer to the first named definition or type declaration above the current line."]
    Just name -> do
      prog' <- insertWithM dupDef name
        (Just (Definition $ pure $ Wet.DefLine pats expr, loc), Nothing)
        prog
      return (prog', Just name)
  ParsedTypeDecl name typ -> do
    prog' <- insertWithM dupDef name
      (Nothing, Just (typ, loc))
      prog
    return (prog', Just name)
  ParsedData name params dataDef -> do
    let pats = (\(p, n, t) -> (p, AnnoPat t $ VarPat (nameHint n) n)) <$> params
        typ = Wet.pis pats (App (Global Builtin.TypeName) Implicit Wildcard)
        tele = (\(p, n, t) -> (p, n, t)) <$> params
    prog' <- insertWithM dupDef name
      (Just (DataDefinition tele dataDef, loc), Just (typ, loc))
      prog
    return (prog', Nothing)
  where
    dupDef :: MaybeTypedDef -> MaybeTypedDef -> Except Text MaybeTypedDef
    dupDef new old = case new of
      (Nothing, Nothing) -> return old
      (Nothing, newType@(Just (_, newLoc))) -> case old of
        (Just (DataDefinition _ _, oldLoc), _) -> do
          let r = render oldLoc
          err
            newLoc
            "Superfluous type signature"
            [ "Data definitions cannot have free-standing type declarations."
            , "Previous definition at " <> Leijen.pretty (delta r) <> ":"
            , Leijen.pretty r
            ]
        (oldDef, Nothing) -> return (oldDef, newType)
        (_oldDef, Just (_, oldLoc)) -> do
          let r = render oldLoc
          err
            newLoc
            "Duplicate type signature"
            [ "Previous signature at " <> Leijen.pretty (delta r) <> ":"
            , Leijen.pretty r
            ]
      (newDef@(Just (_, newLoc)), Nothing) -> case old of
        (Nothing, oldType) -> return (newDef, oldType)
        (Just (_, oldLoc), _oldType) -> do
          let r = render oldLoc
          err
            newLoc
            "Duplicate definition"
            [ "Previous definition at " <> Leijen.pretty (delta r) <> ":"
            , Leijen.pretty r
            ]
      (Just (_, newLoc), Just _) -> case old of
        (Nothing, Nothing) -> return new
        (Just (_, oldLoc), _oldType) -> do
          let r = render oldLoc
          err
            newLoc
            "Duplicate definition"
            [ "Previous definition at " <> Leijen.pretty (delta r) <> ":"
            , Leijen.pretty r
            ]
        (_oldDef, Just (_, oldLoc)) -> do
          let r = render oldLoc
          err
            newLoc
            "Duplicate type signature"
            [ "Previous signature at " <> Leijen.pretty (delta r) <> ":"
            , Leijen.pretty r
            ]

insertWithM
  :: (Eq k, Hashable k, Monad m)
  => (v -> v -> m v) -> k -> v -> HashMap k v -> m (HashMap k v)
insertWithM f k new m = case HM.lookup k m of
  Just old -> do
    new' <- f new old
    return $ HM.insert k new' m
  Nothing -> return $ HM.insert k new m

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
