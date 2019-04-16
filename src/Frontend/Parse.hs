{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
module Frontend.Parse where

import Protolude hiding (Type, moduleName)

import Control.Applicative((<**>), (<|>), Alternative)
import Data.Char
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Set as Set
import Data.String
import Data.Text(Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector
import qualified Text.Parser.LookAhead as LookAhead
import qualified Text.Parser.Token.Highlight as Highlight
import qualified Text.Parsix as Parsix
import Text.Parsix(Position(Position, visualRow, visualColumn), (<?>))
import Text.Parsix.Highlight(Highlights)

import Error
import SourceLoc
import Syntax hiding (classDef, dataDef)
import Syntax.Pre.Literal as Pre
import Syntax.Pre.Unscoped as Pre
import Util

data ParseEnv = ParseEnv
  { parseEnvIndentAnchor :: !Position
  , parseEnvSourceFile :: FilePath
  , parseEnvModuleName :: !ModuleName
  , parseEnvRelativeToName :: !(Maybe (QName, Position))
  }

newtype Parser a = Parser {runParser :: ReaderT ParseEnv Parsix.Parser a}
  deriving
    ( Monad, MonadPlus, MonadReader ParseEnv, Functor, Applicative, Alternative
    , Parsix.Parsing, Parsix.CharParsing, Parsix.SliceParsing, Parsix.RecoveryParsing
    , LookAhead.LookAheadParsing
    )

parseTest :: (MonadIO m, Show a) => Parser a -> String -> m ()
parseTest p s = liftIO $ print $ parseText p (fromString s) "<interactive>"

parseText :: Parser a -> Text -> FilePath -> (Either Error a, Highlights)
parseText p s fp =
  case Parsix.parseText ((,) <$> runReaderT (runParser p) env <* Parsix.eof <*> Parsix.highlights) s fp of
    Parsix.Failure e ->
      (Left
        $ SyntaxError
          (pretty $ fromMaybe mempty $ Parsix.errorReason e)
          (Just loc)
          $ case Set.toList $ Parsix.errorExpected e of
            [] -> mempty
            expected -> "expected:" PP.<+> PP.hsep (PP.punctuate PP.comma $ PP.pretty <$> expected)
      , Parsix.errorHighlights e
      )
      where
        loc = Absolute AbsoluteSourceLoc
          { absoluteFile = Parsix.errorFilePath e
          , absoluteSpan = Parsix.Span (Parsix.errorPosition e) (Parsix.errorPosition e)
          , absoluteHighlights = Just $ Parsix.errorHighlights e
          }
    Parsix.Success (a, highlights) -> (Right a, highlights)
  where
    env = ParseEnv
      { parseEnvIndentAnchor = Position 0 0 0
      , parseEnvSourceFile = fp
      , parseEnvRelativeToName = Nothing
      , parseEnvModuleName = ""
      }

parseFromFileEx :: MonadIO m => Parser a -> FilePath -> m (Either Error a, Highlights)
parseFromFileEx p fp = do
  s <- liftIO $ Text.readFile fp
  return $ parseText p s fp

instance Parsix.TokenParsing Parser where
  someSpace = Parsix.skipSome (Parsix.satisfy isSpace) *> (comments <|> pure ())
           <|> comments
    where
      comments = Parsix.highlight Highlight.Comment (lineComment <|> multilineComment) *> Parsix.whiteSpace
  highlight h (Parser p) = Parser $ Parsix.highlight h p

lineComment :: Parser ()
lineComment =
  () <$ Parsix.string "--"
     <* Parsix.manyTill Parsix.anyChar (Parsix.char '\n')
     <?> "line comment"

multilineComment :: Parser ()
multilineComment =
  () <$ Parsix.string "{-" <* inner
  <?> "multi-line comment"
  where
    inner =  Parsix.string "-}"
         <|> multilineComment *> inner
         <|> Parsix.anyChar *> inner

manyIndexed :: (Int -> Parser a) -> Parser [a]
manyIndexed f = go 0
  where
    go !i
      = (:) <$> f i <*> go (i + 1)
      <|> pure []

-------------------------------------------------------------------------------
-- * Indentation parsing

-- | Drop the indentation anchor -- use the current position as the reference
--   point in the given parser.
dropAnchor :: Parser a -> Parser a
dropAnchor p = do
  pos <- Parsix.position
  local (\env -> env { parseEnvIndentAnchor = pos }) p

-- | Check that the current indentation level is the same as the anchor
sameCol :: Parser ()
sameCol = do
  pos <- Parsix.position
  anchor <- asks parseEnvIndentAnchor
  case comparing visualColumn pos anchor of
    LT -> Parsix.unexpected "unindent"
    EQ -> return ()
    GT -> Parsix.unexpected "indent"

-- | Check that the current indentation level is on the same line as the anchor
--   or on a successive line but more indented.
sameLineOrIndented :: Parser ()
sameLineOrIndented = do
  pos <- Parsix.position
  anchor <- asks parseEnvIndentAnchor
  case (comparing visualRow pos anchor, comparing visualColumn pos anchor) of
    (EQ, _) -> return () -- Same line
    (GT, GT) -> return () -- Indented
    (_,  _) -> Parsix.unexpected "unindent"

-- | One or more at the same indentation level.
someSameCol :: Parser a -> Parser [a]
someSameCol p = Parsix.some (sameCol >> p)

-- | Zero or more at the same indentation level.
manySameCol :: Parser a -> Parser [a]
manySameCol p = Parsix.many (sameCol >> p)

manyIndentedOrSameCol :: Parser a -> Parser [a]
manyIndentedOrSameCol p
  = Parsix.option []
  $ sameLineOrIndented >> dropAnchor (someSameCol p)

optionalSI :: Parser a -> Parser (Maybe a)
optionalSI p = Parsix.optional (sameLineOrIndented >> p)

-- | One or more on the same line or a successive but indented line.
someSI :: Parser a -> Parser [a]
someSI p = Parsix.some (sameLineOrIndented >> p)

-- | Zero or more on the same line or a successive but indented line.
manySI :: Parser a -> Parser [a]
manySI p = Parsix.many (sameLineOrIndented >> p)

sepBySI :: Parser a -> Parser sep -> Parser [a]
sepBySI p sep = (:) <$> p <*> manySI (sep *>% p)

-- * Applicative style combinators for checking that the second argument parser
--   is on the same line or indented compared to the anchor.
infixl 4 <$>%, <$%, <*>%, <*%, *>%, <**>%
(<$>%) :: (a -> b) -> Parser a -> Parser b
f <$>% p = f <$> (sameLineOrIndented >> p)
(<$%) :: a -> Parser b -> Parser a
f <$% p = f <$ (sameLineOrIndented >> p)
(<*>%) :: Parser (a -> b) -> Parser a -> Parser b
p <*>%q = p <*> (sameLineOrIndented >> q)
(<*%) :: Parser a -> Parser b -> Parser a
p <*% q = p <* (sameLineOrIndented >> q)
(*>%) :: Parser a -> Parser b -> Parser b
p *>% q = p *> (sameLineOrIndented >> q)
(<**>%) :: Parser a -> Parser (a -> b) -> Parser b
p <**>% q = p <**> (sameLineOrIndented >> q)

-------------------------------------------------------------------------------
-- * Error recovery
recover :: (Error -> a) -> Parsix.ErrorInfo -> Parsix.Position -> Parser a
recover k errInfo pos = do
  file <- asks parseEnvSourceFile
  skipToAnchorLevel
  highlights <- Parser $ lift $ Parsix.highlights
  let reason = pretty $ fromMaybe mempty $ Parsix.errorInfoReason errInfo
      expected = case Set.toList $ Parsix.errorInfoExpected errInfo of
        [] -> mempty
        xs -> "expected:" PP.<+> PP.hsep (PP.punctuate PP.comma $ PP.pretty <$> xs)
  return
    $ k
    $ SyntaxError
      reason
      (Just $ Absolute AbsoluteSourceLoc
        { absoluteFile = file
        , absoluteSpan = Parsix.Span pos pos
        , absoluteHighlights = Just highlights
        }
      )
      expected

skipToAnchorLevel :: Parser ()
skipToAnchorLevel = Parsix.token $ Parsix.skipSome (sameLineOrIndented >> Parsix.anyChar)

-------------------------------------------------------------------------------
-- * Tokens
idStart, idLetter, qidLetter :: Parser Char
idStart = Parsix.satisfy isAlpha <|> Parsix.oneOf "_"
idLetter = Parsix.satisfy isAlphaNum <|> Parsix.oneOf "_'"
qidLetter = idLetter
  <|> Parsix.try (Parsix.char '.' <* LookAhead.lookAhead idLetter)

reservedIds :: HashSet String
reservedIds = HashSet.fromList ["forall", "_", "case", "of", "let", "in", "where", "abstract", "class", "instance"]

-- TODO Stop using these, roll our own to be able to slice
idStyle :: Parsix.IdentifierStyle Parser
idStyle = Parsix.IdentifierStyle "identifier" idStart idLetter reservedIds Highlight.Identifier Highlight.ReservedIdentifier

qidStyle :: Parsix.IdentifierStyle Parser
qidStyle = Parsix.IdentifierStyle "identifier" idStart qidLetter reservedIds Highlight.Identifier Highlight.ReservedIdentifier

name :: Parser Name
name = Parsix.ident idStyle

qname :: Parser PreName
qname = uncurry PreName . first Just <$> located (Parsix.ident qidStyle)

constructor :: Parser Constr
constructor
  = Parsix.highlight Highlight.Constructor
  $ Parsix.ident idStyle

qconstructor :: Parser PreName
qconstructor
  = Parsix.highlight Highlight.Constructor
  $ uncurry PreName . first Just <$> located (Parsix.ident qidStyle)

modulName :: Parser ModuleName
modulName = Parsix.ident qidStyle

reserved :: Text -> Parser ()
reserved = Parsix.reserveText idStyle

wildcard :: Parser ()
wildcard = reserved "_"

nameOrWildcard :: Parser (Maybe Name)
nameOrWildcard
  = Just <$> name
  <|> Nothing <$ wildcard

symbol :: String -> Parser Name
symbol = fmap fromString . Parsix.symbol

integer :: Parser Integer
integer = Parsix.try Parsix.integer

located :: Parser a -> Parser (SourceLoc, a)
located p = do
  (s, a) <- Parsix.spanned p
  env <- ask
  let
    loc = case parseEnvRelativeToName env of
      Nothing -> Absolute $ AbsoluteSourceLoc (parseEnvSourceFile env) s Nothing
      Just (n, pos) -> Relative $ RelativeSourceLoc n $ spanRelativeTo pos s
  return (loc, a)

-------------------------------------------------------------------------------
-- * Patterns
locatedPat :: Parser (Pat c l typ v) -> Parser (Pat c l typ v)
locatedPat p = uncurry PatLoc <$> located p

pattern :: Parser (Pat PreName Pre.Literal PreName Type)
pattern = locatedPat $
  ( Parsix.try (ConPat <$> qconstructor <*> (Vector.fromList <$> someSI plicitPattern))
    <|> atomicPattern
  ) <**>
  ( flip AnnoPat <$% symbol ":" <*> expr
    <|> pure identity
  ) <?> "pattern"

plicitPattern :: Parser (Plicitness, Pat PreName Pre.Literal PreName Type)
plicitPattern = (,) Implicit <$ symbol "@" <*>% atomicPattern
  <|> (,) Explicit <$> atomicPattern
  <?> "explicit or implicit pattern"

atomicPattern :: Parser (Pat PreName Pre.Literal PreName Type)
atomicPattern = locatedPat
  $ symbol "(" *>% pattern <*% symbol ")"
  <|> ForcedPat <$ symbol "~" <*>% atomicExpr
  <|> VarPat <$> qname
  <|> WildcardPat <$ wildcard
  <|> LitPat <$> literal
  <?> "atomic pattern"

plicitPatternBinding :: Parser [(Plicitness, Pat PreName Pre.Literal PreName Type)]
plicitPatternBinding
  = go Implicit <$ symbol "@" <*% symbol "(" <*> someSI atomicPattern <*% symbol ":" <*>% expr <*% symbol ")"
  <|> go Explicit <$ symbol "(" <*> someSI atomicPattern <*% symbol ":" <*>% expr <*% symbol ")"
  <?> "typed pattern"
  where
    go p pats t = [(p, AnnoPat pat t) | pat <- pats]

patternBinding :: Parser [(Pat PreName Pre.Literal PreName Type)]
patternBinding
  = go <$ symbol "(" <*> someSI atomicPattern <*% symbol ":" <*>% expr <*% symbol ")"
  <?> "typed pattern"
  where
    go pats t = [AnnoPat pat t | pat <- pats]

somePlicitPatternBindings :: Parser [(Plicitness, Pat PreName Pre.Literal PreName Type)]
somePlicitPatternBindings
  = concat <$> someSI plicitPatternBinding

somePlicitPatterns :: Parser [(Plicitness, Pat PreName Pre.Literal PreName Type)]
somePlicitPatterns
  = concat <$> someSI (Parsix.try plicitPatternBinding <|> pure <$> plicitPattern)

somePatterns :: Parser [(Pat PreName Pre.Literal PreName Type)]
somePatterns
  = concat <$> someSI (Parsix.try patternBinding <|> pure <$> atomicPattern)

manyPlicitPatterns :: Parser [(Plicitness, Pat PreName Pre.Literal PreName Type)]
manyPlicitPatterns
  = concat <$> manySI (Parsix.try plicitPatternBinding <|> pure <$> plicitPattern)

plicitBinding :: Parser (Plicitness, Name)
plicitBinding
  = (,) Implicit <$ symbol "@" <*>% name
  <|> (,) Explicit <$> name
  <?> "variable binding"

plicitBinding' :: Parser [(Plicitness, Name, Type)]
plicitBinding'
  = (\(p, n) -> [(p, n, Wildcard)]) <$> plicitBinding

typedBinding :: Parser [(Plicitness, Name, Type)]
typedBinding = fmap flatten
  $ (,,) Implicit <$ symbol "@" <*% symbol "(" <*> someSI name <*% symbol ":" <*>% expr <*% symbol ")"
  <|> (,,) Explicit <$ symbol "(" <*> someSI name <*% symbol ":" <*>% expr <*% symbol ")"
  <?> "typed variable binding"
  where
    flatten (p, names, t) = [(p, n, t) | n <- names]

manyTypedBindings :: Parser [(Plicitness, Name, Type)]
manyTypedBindings = concat <$> manySI (Parsix.try typedBinding <|> plicitBinding')

-------------------------------------------------------------------------------
-- * Expressions
locatedExpr :: Parser Expr -> Parser Expr
locatedExpr p = uncurry SourceLoc <$> located p

atomicExpr :: Parser Expr
atomicExpr = locatedExpr
  $ Lit <$> literal
  <|> Wildcard <$ wildcard
  <|> Var <$> qname
  <|> Pre.pis <$ reserved "forall" <*>% (fmap ((,) Implicit) <$> somePatterns) <*% symbol "." <*>% exprWithoutWhere
  <|> Pre.lams <$ symbol "\\" <*>% somePlicitPatterns <*% symbol "." <*>% exprWithoutWhere
  <|> Case <$ reserved "case" <*>% expr <*% reserved "of" <*> branches
  <|> letExpr
  <|> ExternCode <$> externCExpr
  <|> symbol "(" *>% expr <*% symbol ")"
  <?> "atomic expression"
  where
    letExpr
      = dropAnchor
      $ mkLet <$ reserved "let" <*>% dropAnchor (someSameCol localConstantDef)
      <*>
        ((sameLineOrIndented <|> sameCol) *> reserved "in" *>% exprWithoutWhere
        <|> sameCol *> exprWithoutWhere
        )
      where
        mkLet xs = Let $ Vector.fromList xs

branches :: Parser [(SourceLoc, Pat PreName Pre.Literal PreName Type, Expr)]
branches = manyIndentedOrSameCol branch
  where
    branch = fmap mkBranch $ located $ (,) <$> pattern <*% symbol "->" <*>% expr
    mkBranch (loc, (pat, e)) = (loc, pat, e)

expr :: Parser Expr
expr = exprWithoutWhere <**>
  (mkLet <$% reserved "where" <*>% dropAnchor (someSameCol localConstantDef)
  <|> pure identity
  )
  where
    mkLet xs = Let $ Vector.fromList xs

exprWithRecoverySI :: Parser Expr
exprWithRecoverySI = Parsix.withRecovery (recover Pre.Error) (sameLineOrIndented >> expr)

exprWithoutWhere :: Parser Expr
exprWithoutWhere
  = locatedExpr
  $ Pre.pis <$> Parsix.try (somePlicitPatternBindings <*% symbol "->") <*>% exprWithoutWhere
  <|> Pre.apps <$> atomicExpr <*> manySI argument <**> arr
  <|> plicitPi Implicit <$ symbol "@" <*>% atomicExpr <*% symbol "->" <*>% exprWithoutWhere
  <?> "expression"
  where
    plicitPi p argType retType = Pi p (AnnoPat WildcardPat argType) retType

    arr
      = flip (plicitPi Explicit) <$% symbol "->" <*>% exprWithoutWhere
      <|> flip (plicitPi Constraint) <$% symbol "=>" <*>% exprWithoutWhere
      <|> pure identity

    argument :: Parser (Plicitness, Expr)
    argument
      = (,) Implicit <$ symbol "@" <*>% atomicExpr
      <|> (,) Explicit <$> atomicExpr

-------------------------------------------------------------------------------
-- * Extern C
externCExpr :: Parser (Extern Expr)
externCExpr
  = Extern C . fmap (either identity $ ExternPart . Text.pack) <$ Parsix.string "(C|" <*> go
  <?> "Extern C expression"
  where
    go = Parsix.char '\\' *> escaped <*> go
      <|> (:) <$ Parsix.char '$' <*> (Left <$> macroPart) <*> go
      <|> [] <$ symbol "|)"
      <|> consChar <$> Parsix.anyChar <*> go
    macroPart
      = TargetMacroPart PointerAlignment <$ Parsix.string "target:" <* Parsix.string "pointerAlignment"
      <|> TypeMacroPart <$ Parsix.string "type:" <*> atomicExpr
      <|> ExprMacroPart <$> atomicExpr
    consChar c (Right t : rest) = Right (c:t) : rest
    consChar c rest = Right [c] : rest
    consChars = foldr (\c -> (consChar c .)) identity
    escaped
      = consChar <$> Parsix.char '$'
      <|> consChars <$> Parsix.string "|)"
      <|> (\c -> consChars ('\\' : [c])) <$> Parsix.anyChar

-------------------------------------------------------------------------------
-- * Literals
literal :: Parser Pre.Literal
literal
  = Pre.Integer <$> integer
  <|> Pre.String <$> Parsix.stringLiteral

-------------------------------------------------------------------------------
-- * Definitions
-- | A definition or type declaration on the top-level
def :: Int -> Parser (Either Error (QName, AbsoluteSourceLoc, Pre.Definition))
def i = Parsix.withRecovery (recover Left)
  $ fmap Right
  $ dataDef
  <|> classDef
  <|> instanceDef i
  <|> second Pre.ConstantDefinition <$> constantDef positionedRelativeTo

constantDef
  :: (Name -> Parsix.Position -> Parser (Pre.ConstantDef Pre.Expr) -> Parser a)
  -> Parser a
constantDef k = do
  pos <- Parsix.position
  abstr
    <- Abstract <$ reserved "abstract" <* sameCol
    <|> pure Concrete
  dropAnchor $ do
    n <- name
    sameLineOrIndented
    k n pos $ do
      let namedClause
            = dropAnchor
            $ (wildcard <|> void (reserved $ fromName n))
            *>% clause -- Parsix.withRecovery (recover $ Pre.Clause mempty . Pre.Error) clause
      (mtyp, clauses)
        <- (,) . Just <$> typeSig <*> someSameCol namedClause
        <|> (,) Nothing <$> ((:) <$> clause <*> manySameCol namedClause)
      return (Pre.ConstantDef abstr (NonEmpty.fromList clauses) mtyp)
  where
    typeSig = symbol ":" *> exprWithRecoverySI
    clause = fmap mkClause $ located $ (,) <$> (Vector.fromList <$> manyPlicitPatterns) <*% symbol "=" <*> exprWithRecoverySI
    mkClause (loc, (pats, e)) = Clause loc pats e

localConstantDef :: Parser (Name, SourceLoc, Pre.ConstantDef Pre.Expr)
localConstantDef = do
  (loc, (n, d)) <- located $ constantDef $ \n _ p -> (,) n <$> p
  return (n, loc, d)

dataDef :: Parser (QName, AbsoluteSourceLoc, Pre.Definition)
dataDef = do
  pos <- Parsix.position
  boxed
    <- Boxed <$ reserved "boxed" <* sameCol
    <|> pure Unboxed
  n <- reserved "type" *>% name
  positionedRelativeTo n pos $
    Pre.DataDefinition boxed <$> manyTypedBindings <*>%
      (concat <$% reserved "where" <*> manyIndentedOrSameCol conDef
      <|> identity <$% symbol "=" <*>% sepBySI adtConDef (symbol "|"))
  where
    conDef = constrDefs <$> ((:) <$> constructor <*> manySI constructor)
      <*% symbol ":" <*>% expr
    constrDefs cs t = [GADTConstrDef c t | c <- cs]
    adtConDef = ADTConstrDef <$> constructor <*> manySI atomicExpr

classDef :: Parser (QName, AbsoluteSourceLoc, Pre.Definition)
classDef = do
  pos <- Parsix.position
  n <- reserved "class" *>% name
  positionedRelativeTo n pos $
    Pre.ClassDefinition
      <$> manyTypedBindings
      <*% reserved "where" <*> manyIndentedOrSameCol (mkMethodDef <$> located ((,) <$> name <*% symbol ":" <*>% expr))
  where
  mkMethodDef (loc, (n, e)) = Method n loc e

instanceDef :: Int -> Parser (QName, AbsoluteSourceLoc, Pre.Definition)
instanceDef i = do
  pos <- Parsix.position
  let
    n = "instance-" <> shower i
  positionedRelativeTo n pos $
    InstanceDefinition <$ reserved "instance" <*>% exprWithoutWhere
      <*% reserved "where" <*> manyIndentedOrSameCol localConstantDef

positionedRelativeTo
  :: Name
  -> Parsix.Position
  -> Parser a
  -> Parser (QName, AbsoluteSourceLoc, a)
positionedRelativeTo n startPos p = do
  env <- ask
  let
    mname = parseEnvModuleName env
    file = parseEnvSourceFile env
    qn = QName mname n
  a <- local (\env' -> env' { parseEnvRelativeToName = Just (qn, startPos) }) p
  endPos <- Parsix.position
  return (qn, AbsoluteSourceLoc file (Parsix.Span startPos endPos) Nothing, a)

-------------------------------------------------------------------------------
-- * Module
modul :: Parser (ModuleHeader, [(Either Error (QName, AbsoluteSourceLoc, Pre.Definition))])
modul = do
  Parsix.whiteSpace
  dropAnchor $ do
    header <- moduleHeader
    ds <- local (\env -> env { parseEnvModuleName = moduleName header }) $
      manyIndexed $ \i -> do
        sameCol
        dropAnchor $ def i
    return (header, ds)

moduleHeader :: Parser ModuleHeader
moduleHeader = moduleExposing <*> manySameCol (dropAnchor impor)
  where
    moduleExposing
      = ModuleHeader <$ reserved "module" <*>% modulName <*% reserved "exposing" <*>% exposedNames
      <|> pure (ModuleHeader "Main" AllExposed)

impor :: Parser Import
impor
  = go <$ reserved "import" <*>% modulName
  <*> optionalSI
    (reserved "as" *>% modulName)
  <*> optionalSI
    (reserved "exposing" *>% exposedNames)
  where
    go n malias mexposed = Import n (fromMaybe n malias) (fromMaybe noneExposed mexposed)

exposedNames :: Parser ExposedNames
exposedNames = symbol "(" *>% go <*% symbol ")"
  where
    go
      = AllExposed <$ symbol ".."
      <|> Exposed . HashSet.fromList <$> sepBySI name (symbol ",")
      <|> pure (Exposed mempty)
