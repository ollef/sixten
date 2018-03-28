{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, GeneralizedNewtypeDeriving, OverloadedStrings #-}
module Frontend.Parse where

import Control.Applicative((<**>), (<|>), Alternative)
import Control.Monad.Except
import Control.Monad.Reader
import Data.Char
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.Ord
import qualified Data.Set as Set
import Data.String
import Data.Text(Text)
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector
import qualified Text.Parser.LookAhead as LookAhead
import qualified Text.Parser.Token.Highlight as Highlight
import qualified Text.Parsix as Parsix
import Text.Parsix(Position(Position, visualRow, visualColumn), (<?>))

import Error
import Processor.Result
import Syntax
import Syntax.Concrete.Literal
import Syntax.Concrete.Pattern
import Syntax.Concrete.Unscoped as Unscoped

data ParseEnv = ParseEnv
  { parseEnvIndentAnchor :: !Position
  , parseEnvSourceFile :: FilePath
  }

newtype Parser a = Parser {runParser :: ReaderT ParseEnv Parsix.Parser a}
  deriving
    ( Monad, MonadPlus, MonadReader ParseEnv, Functor, Applicative, Alternative
    , Parsix.Parsing, Parsix.CharParsing, Parsix.SliceParsing, Parsix.RecoveryParsing
    , LookAhead.LookAheadParsing
    )

parseTest :: (MonadIO m, Show a) => Parser a -> String -> m ()
parseTest p = Parsix.parseTest $ runReaderT (runParser p) env <* Parsix.eof
  where
    env = ParseEnv (Position 0 0 0) "<interactive>"

parseFromFileEx :: MonadIO m => Parser a -> FilePath -> m (Result a)
parseFromFileEx p fp = do
  res <- Parsix.parseFromFileEx (runReaderT (runParser p) env <* Parsix.eof) fp
  return $ case res of
    Parsix.Failure e -> Failure
      $ pure
      $ SyntaxError
        (pretty $ fromMaybe mempty $ Parsix.errorReason e)
        (Just loc)
        $ case Set.toList $ Parsix.errorExpected e of
          [] -> mempty
          expected -> "expected:" PP.<+> PP.hsep (PP.punctuate PP.comma $ PP.pretty <$> expected)
      where
        loc = SourceLocation
          { sourceLocFile = Parsix.errorFilePath e
          , sourceLocSpan = Parsix.Span (Parsix.errorPosition e) (Parsix.errorPosition e)
          , sourceLocSource = Parsix.errorSourceText e
          , sourceLocHighlights = Parsix.errorHighlights e
          }
    Parsix.Success a -> return a
  where
    env = ParseEnv (Position 0 0 0) fp

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
recover :: (Error -> a) -> Parsix.ErrorInfo -> Parser a
recover k errInfo = do
  (loc, _) <- located skipToAnchorLevel
  let reason = pretty $ fromMaybe mempty $ Parsix.errorInfoReason errInfo
      expected = case Set.toList $ Parsix.errorInfoExpected errInfo of
        [] -> mempty
        xs -> "expected:" PP.<+> PP.hsep (PP.punctuate PP.comma $ PP.pretty <$> xs)
  return $ k $ SyntaxError reason (Just loc) expected

skipToAnchorLevel :: Parser ()
skipToAnchorLevel = Parsix.skipMany (sameLineOrIndented >> Parsix.anyChar)

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
qname = Parsix.ident qidStyle

constructor :: Parser Constr
constructor
  = Parsix.highlight Highlight.Constructor
  $ Parsix.ident idStyle

qconstructor :: Parser PreName
qconstructor
  = Parsix.highlight Highlight.Constructor
  $ Parsix.ident qidStyle

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
  (s, a) <- Parsix.highlight Highlight.Constructor $ Parsix.spanned p
  file <- asks parseEnvSourceFile
  inp <- Parser $ lift Parsix.input
  hl <- Parser $ lift Parsix.highlights
  return (SourceLocation file s inp hl, a)

-------------------------------------------------------------------------------
-- * Patterns
locatedPat :: Parser (Pat c typ v) -> Parser (Pat c typ v)
locatedPat p = uncurry PatLoc <$> located p

pattern :: Parser (Pat PreName Type PreName)
pattern = locatedPat $
  ( Parsix.try (ConPat <$> qconstructor <*> (Vector.fromList <$> someSI plicitPattern))
    <|> atomicPattern
  ) <**>
  ( flip AnnoPat <$% symbol ":" <*> expr
    <|> pure id
  ) <?> "pattern"

plicitPattern :: Parser (Plicitness, Pat PreName Type PreName)
plicitPattern = (,) Implicit <$ symbol "@" <*>% atomicPattern
  <|> (,) Explicit <$> atomicPattern
  <?> "explicit or implicit pattern"

atomicPattern :: Parser (Pat PreName Type PreName)
atomicPattern = locatedPat
  $ symbol "(" *>% pattern <*% symbol ")"
  <|> (\v -> VarPat (fromPreName v) v) <$> qname
  <|> WildcardPat <$ wildcard
  <|> literalPat
  <?> "atomic pattern"

plicitPatternBinding :: Parser [(Plicitness, Pat PreName Type PreName)]
plicitPatternBinding
  = go Implicit <$ symbol "@" <*% symbol "(" <*> someSI atomicPattern <*% symbol ":" <*>% expr <*% symbol ")"
  <|> go Explicit <$ symbol "(" <*> someSI atomicPattern <*% symbol ":" <*>% expr <*% symbol ")"
  <?> "typed pattern"
  where
    go p pats t = [(p, AnnoPat pat t) | pat <- pats]

patternBinding :: Parser [(Pat PreName Type PreName)]
patternBinding
  = go <$ symbol "(" <*> someSI atomicPattern <*% symbol ":" <*>% expr <*% symbol ")"
  <?> "typed pattern"
  where
    go pats t = [AnnoPat pat t | pat <- pats]

somePlicitPatternBindings :: Parser [(Plicitness, Pat PreName Type PreName)]
somePlicitPatternBindings
  = concat <$> someSI plicitPatternBinding

somePlicitPatterns :: Parser [(Plicitness, Pat PreName Type PreName)]
somePlicitPatterns
  = concat <$> someSI (Parsix.try plicitPatternBinding <|> pure <$> plicitPattern)

somePatterns :: Parser [(Pat PreName Type PreName)]
somePatterns
  = concat <$> someSI (Parsix.try patternBinding <|> pure <$> atomicPattern)

manyPlicitPatterns :: Parser [(Plicitness, Pat PreName Type PreName)]
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
  $ literal
  <|> Wildcard <$ wildcard
  <|> Var <$> qname
  <|> Unscoped.pis <$ reserved "forall" <*>% (fmap ((,) Implicit) <$> somePatterns) <*% symbol "." <*>% exprWithoutWhere
  <|> Unscoped.lams <$ symbol "\\" <*>% somePlicitPatterns <*% symbol "." <*>% exprWithoutWhere
  <|> Case <$ reserved "case" <*>% expr <*% reserved "of" <*> branches
  <|> letExpr
  <|> ExternCode <$> externCExpr
  <|> symbol "(" *>% expr <*% symbol ")"
  <?> "atomic expression"
  where
    letExpr
      = dropAnchor
      $ mkLet <$ reserved "let" <*>% dropAnchor (someSameCol $ located def)
      <*>
        ((sameLineOrIndented <|> sameCol) *> reserved "in" *>% exprWithoutWhere
        <|> sameCol *> exprWithoutWhere
        )
      where
        mkLet xs = Let $ Vector.fromList xs

branches :: Parser [(Pat PreName Type PreName, Expr)]
branches = manyIndentedOrSameCol branch
  where
    branch = (,) <$> pattern <*% symbol "->" <*>% expr

expr :: Parser Expr
expr = exprWithoutWhere <**>
  (mkLet <$% reserved "where" <*>% dropAnchor (someSameCol $ located def)
  <|> pure id
  )
  where
    mkLet xs = Let $ Vector.fromList xs

exprWithRecoverySI :: Parser Expr
exprWithRecoverySI = Parsix.withRecovery (recover Unscoped.Error) (sameLineOrIndented >> expr)

exprWithoutWhere :: Parser Expr
exprWithoutWhere
  = locatedExpr
  $ Unscoped.pis <$> Parsix.try (somePlicitPatternBindings <*% symbol "->") <*>% exprWithoutWhere
  <|> Unscoped.apps <$> atomicExpr <*> manySI argument <**> arr
  <|> plicitPi Implicit <$ symbol "@" <*>% atomicExpr <*% symbol "->" <*>% exprWithoutWhere
  <?> "expression"
  where
    plicitPi p argType retType = Pi p (AnnoPat WildcardPat argType) retType

    arr
      = flip (plicitPi Explicit) <$% symbol "->" <*>% exprWithoutWhere
      <|> flip (plicitPi Constraint) <$% symbol "=>" <*>% exprWithoutWhere
      <|> pure id

    argument :: Parser (Plicitness, Expr)
    argument
      = (,) Implicit <$ symbol "@" <*>% atomicExpr
      <|> (,) Explicit <$> atomicExpr

-------------------------------------------------------------------------------
-- * Extern C
externCExpr :: Parser (Extern Expr)
externCExpr
  = Extern C . fmap (either id $ ExternPart . Text.pack) <$ Parsix.string "(C|" <*> go
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
    consChars = foldr (\c -> (consChar c .)) id
    escaped
      = consChar <$> Parsix.char '$'
      <|> consChars <$> Parsix.string "|)"
      <|> (\c -> consChars ('\\' : [c])) <$> Parsix.anyChar

-------------------------------------------------------------------------------
-- * Literals
literal :: Parser Expr
literal
  = Lit . Integer <$> integer
  <|> string <$> Parsix.stringLiteral

literalPat :: Parser (Pat PreName t n)
literalPat
  = LitPat . Integer <$> integer
  <|> stringPat <$> Parsix.stringLiteral

-------------------------------------------------------------------------------
-- * Definitions
-- | A definition or type declaration on the top-level
topLevel :: Parser (SourceLoc, TopLevelDefinition)
topLevel = located
  $ dataDef
  <|> classDef
  <|> instanceDef
  <|> TopLevelDefinition <$> def

def :: Parser (Unscoped.Definition Unscoped.Expr)
def = do
  abstr
    <- Abstract <$ reserved "abstract" <* sameCol
    <|> pure Concrete
  dropAnchor $ do
    n <- name
    sameLineOrIndented
    let namedClause
          = dropAnchor
          $ (wildcard <|> void (reserved $ fromName n))
          *>% clause -- Parsix.withRecovery (recover $ Unscoped.Clause mempty . Unscoped.Error) clause
    (mtyp, clauses)
      <- (,) . Just <$> typeSig <*> someSameCol namedClause
      <|> (,) Nothing <$> ((:) <$> clause <*> manySameCol namedClause)
    return (Unscoped.Definition n abstr (NonEmpty.fromList clauses) mtyp)
  where
    typeSig = symbol ":" *> exprWithRecoverySI
    clause = Clause <$> (Vector.fromList <$> manyPlicitPatterns) <*% symbol "=" <*> exprWithRecoverySI

dataDef :: Parser TopLevelDefinition
dataDef = TopLevelDataDefinition <$ reserved "type" <*>% name <*> manyTypedBindings <*>%
  (concat <$% reserved "where" <*> manyIndentedOrSameCol conDef
  <|> id <$% symbol "=" <*>% sepBySI adtConDef (symbol "|"))
  where
    conDef = constrDefs <$> ((:) <$> constructor <*> manySI constructor)
      <*% symbol ":" <*>% expr
    constrDefs cs t = [ConstrDef c t | c <- cs]
    adtConDef = ConstrDef <$> constructor <*> (adtConType <$> manySI atomicExpr)
    adtConType es = Unscoped.pis ((\e -> (Explicit, AnnoPat WildcardPat e)) <$> es) Wildcard

classDef :: Parser TopLevelDefinition
classDef = TopLevelClassDefinition <$ reserved "class" <*>% name <*> manyTypedBindings
  <*% reserved "where" <*> manyIndentedOrSameCol (mkMethodDef <$> located ((,) <$> name <*% symbol ":" <*>% expr))
  where
    mkMethodDef (loc, (n, e)) = MethodDef n loc e


instanceDef :: Parser TopLevelDefinition
instanceDef = TopLevelInstanceDefinition <$ reserved "instance" <*>% exprWithoutWhere
  <*% reserved "where" <*> manyIndentedOrSameCol (located def)

-------------------------------------------------------------------------------
-- * Module
modul :: Parser (Module [(SourceLoc, Unscoped.TopLevelDefinition)])
modul = Parsix.whiteSpace >> dropAnchor
  ((Module <$ reserved "module" <*>% modulName <*% reserved "exposing" <*>% exposedNames
     <|> pure (Module "Main" AllExposed))
  <*> manySameCol (dropAnchor impor)
  <*> manySameCol (dropAnchor topLevel))

impor :: Parser Import
impor
  = go <$ reserved "import" <*>% modulName
  <*> optionalSI
    (reserved "as" *>% modulName)
  <*> optionalSI
    (reserved "exposing" *>% exposedNames)
  where
    go n malias mexposed = Import n (fromMaybe n malias) (fromMaybe mempty mexposed)

exposedNames :: Parser ExposedNames
exposedNames = symbol "(" *>% go <*% symbol ")"
  where
    go
      = AllExposed <$ symbol ".."
      <|> Exposed . HashSet.fromList <$> sepBySI name (symbol ",")
      <|> pure (Exposed mempty)
