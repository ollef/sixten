{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, GeneralizedNewtypeDeriving, OverloadedStrings #-}
module Frontend.Parse where

import Control.Applicative((<**>), (<|>), Alternative)
import Control.Monad.Except
import Control.Monad.State
import Data.Char
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.Maybe
import Data.Ord
import Data.String
import Data.Text(Text)
import qualified Data.Text as Text
import qualified Data.Vector as Vector
import qualified Data.List.NonEmpty as NonEmpty
import qualified Text.Parser.LookAhead as LookAhead
import qualified Text.Parser.Token.Highlight as Highlight
import qualified Text.Trifecta as Trifecta
import Text.Trifecta((<?>))
import Text.Trifecta.Delta

import Syntax
import Syntax.Concrete.Literal
import Syntax.Concrete.Pattern
import Syntax.Concrete.Unscoped as Unscoped

type Input = Text
newtype Parser a = Parser {runParser :: StateT Delta Trifecta.Parser a}
  deriving
    ( Monad, MonadPlus, MonadState Delta, Functor, Applicative, Alternative
    , Trifecta.Parsing, Trifecta.CharParsing, Trifecta.DeltaParsing
    , LookAhead.LookAheadParsing
    )

parseString :: Parser a -> String -> Trifecta.Result a
parseString p
  = Trifecta.parseString (evalStateT (runParser p) mempty <* Trifecta.eof) mempty

parseFromFile :: MonadIO m => Parser a -> FilePath -> m (Maybe a)
parseFromFile p
  = Trifecta.parseFromFile
  $ evalStateT (runParser p) mempty <* Trifecta.eof

parseFromFileEx :: MonadIO m => Parser a -> FilePath -> m (Trifecta.Result a)
parseFromFileEx p
  = Trifecta.parseFromFileEx
  $ evalStateT (runParser p) mempty <* Trifecta.eof

instance Trifecta.TokenParsing Parser where
  someSpace = Trifecta.skipSome (Trifecta.satisfy isSpace) *> (comments <|> pure ())
           <|> comments
    where
      comments = Trifecta.highlight Highlight.Comment (lineComment <|> multilineComment) *> Trifecta.whiteSpace

lineComment :: Parser ()
lineComment =
  () <$ Trifecta.string "--"
     <* Trifecta.manyTill Trifecta.anyChar (Trifecta.char '\n')
     <?> "line comment"

multilineComment :: Parser ()
multilineComment =
  () <$ Trifecta.string "{-" <* inner
  <?> "multi-line comment"
  where
    inner =  Trifecta.string "-}"
         <|> multilineComment *> inner
         <|> Trifecta.anyChar *> inner

-------------------------------------------------------------------------------
-- * Indentation parsing
deltaLine :: Delta -> Int
deltaLine Columns {} = 0
deltaLine Tab {} = 0
deltaLine (Lines l _ _ _) = fromIntegral l + 1
deltaLine (Directed _ l _ _ _) = fromIntegral l + 1

deltaColumn :: Delta -> Int
deltaColumn pos = fromIntegral (column pos) + 1

-- | Drop the indentation anchor -- use the current position as the reference
--   point in the given parser.
dropAnchor :: Parser a -> Parser a
dropAnchor p = do
  oldAnchor <- get
  pos <- Trifecta.position
  put pos
  result <- p
  put oldAnchor
  return result

-- | Check that the current indentation level is the same as the anchor
sameCol :: Parser ()
sameCol = do
  pos <- Trifecta.position
  anchor <- get
  case comparing deltaColumn pos anchor of
    LT -> Trifecta.unexpected "unindent"
    EQ -> return ()
    GT -> Trifecta.unexpected "indent"

-- | Check that the current indentation level is on the same line as the anchor
--   or on a successive line but more indented.
sameLineOrIndented :: Parser ()
sameLineOrIndented = do
  pos <- Trifecta.position
  anchor <- get
  case (comparing deltaLine pos anchor, comparing deltaColumn pos anchor) of
    (EQ, _) -> return () -- Same line
    (GT, GT) -> return () -- Indented
    (_,  _) -> Trifecta.unexpected "unindent"

-- | One or more at the same indentation level.
someSameCol :: Parser a -> Parser [a]
someSameCol p = Trifecta.some (sameCol >> p)

-- | Zero or more at the same indentation level.
manySameCol :: Parser a -> Parser [a]
manySameCol p = Trifecta.many (sameCol >> p)

manyIndentedOrSameCol :: Parser a -> Parser [a]
manyIndentedOrSameCol p
  = Trifecta.option []
  $ sameLineOrIndented >> dropAnchor (someSameCol p)

optionalSI :: Parser a -> Parser (Maybe a)
optionalSI p = Trifecta.optional (sameLineOrIndented >> p)

-- | One or more on the same line or a successive but indented line.
someSI :: Parser a -> Parser [a]
someSI p = Trifecta.some (sameLineOrIndented >> p)

-- | Zero or more on the same line or a successive but indented line.
manySI :: Parser a -> Parser [a]
manySI p = Trifecta.many (sameLineOrIndented >> p)

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
-- * Tokens
idStart, idLetter, qidLetter :: Parser Char
idStart = Trifecta.satisfy isAlpha <|> Trifecta.oneOf "_"
idLetter = Trifecta.satisfy isAlphaNum <|> Trifecta.oneOf "_'"
qidLetter = idLetter
  <|> Trifecta.try (Trifecta.char '.' <* LookAhead.lookAhead idLetter)

reservedIds :: HashSet String
reservedIds = HashSet.fromList ["forall", "_", "case", "of", "let", "in", "where", "abstract", "class", "instance"]

idStyle :: Trifecta.IdentifierStyle Parser
idStyle = Trifecta.IdentifierStyle "identifier" idStart idLetter reservedIds Highlight.Identifier Highlight.ReservedIdentifier

qidStyle :: Trifecta.IdentifierStyle Parser
qidStyle = Trifecta.IdentifierStyle "identifier" idStart qidLetter reservedIds Highlight.Identifier Highlight.ReservedIdentifier

name :: Parser Name
name = Trifecta.ident idStyle

qname :: Parser QName
qname = Trifecta.ident qidStyle

constructor :: Parser Constr
constructor = Trifecta.ident idStyle

qconstructor :: Parser QConstr
qconstructor = Trifecta.ident qidStyle

modulName :: Parser ModuleName
modulName = Trifecta.ident qidStyle

reserved :: String -> Parser ()
reserved = Trifecta.reserve idStyle

wildcard :: Parser ()
wildcard = reserved "_"

nameOrWildcard :: Parser (Maybe Name)
nameOrWildcard
  = Just <$> name
  <|> Nothing <$ wildcard

symbol :: String -> Parser Name
symbol = fmap fromString . Trifecta.symbol

integer :: Parser Integer
integer = Trifecta.try Trifecta.integer

located :: Parser a -> Parser (SourceLoc, a)
located p = (\(e Trifecta.:~ s) -> (Trifecta.render s, e)) <$> Trifecta.spanned p

-------------------------------------------------------------------------------
-- * Patterns
locatedPat :: Parser (Pat typ v) -> Parser (Pat typ v)
locatedPat p = uncurry PatLoc <$> located p

pattern :: Parser (Pat Type QName)
pattern = locatedPat $
  ( Trifecta.try (ConPat <$> (HashSet.singleton <$> qconstructor) <*> (Vector.fromList <$> someSI plicitPattern))
    <|> atomicPattern
  ) <**>
  ( AnnoPat <$% symbol ":" <*> expr
    <|> pure id
  ) <?> "pattern"

plicitPattern :: Parser (Plicitness, Pat Type QName)
plicitPattern = (,) Implicit <$ symbol "@" <*>% atomicPattern
  <|> (,) Explicit <$> atomicPattern
  <?> "explicit or implicit pattern"

atomicPattern :: Parser (Pat Type QName)
atomicPattern = locatedPat
  $ symbol "(" *>% pattern <*% symbol ")"
  <|> (\v -> VarPat (fromQName v) v) <$> qname
  <|> WildcardPat <$ wildcard
  <|> literalPat
  <?> "atomic pattern"

plicitPatternBinding :: Parser [(Plicitness, Pat Type QName)]
plicitPatternBinding
  = go Implicit <$ symbol "@" <*% symbol "(" <*> someSI atomicPattern <*% symbol ":" <*>% expr <*% symbol ")"
  <|> go Explicit <$ symbol "(" <*> someSI atomicPattern <*% symbol ":" <*>% expr <*% symbol ")"
  <?> "typed pattern"
  where
    go p pats t = [(p, AnnoPat t pat) | pat <- pats]

patternBinding :: Parser [(Pat Type QName)]
patternBinding
  = go <$ symbol "(" <*> someSI atomicPattern <*% symbol ":" <*>% expr <*% symbol ")"
  <?> "typed pattern"
  where
    go pats t = [AnnoPat t pat | pat <- pats]

somePlicitPatternBindings :: Parser [(Plicitness, Pat Type QName)]
somePlicitPatternBindings
  = concat <$> someSI plicitPatternBinding

somePlicitPatterns :: Parser [(Plicitness, Pat Type QName)]
somePlicitPatterns
  = concat <$> someSI (Trifecta.try plicitPatternBinding <|> pure <$> plicitPattern)

somePatterns :: Parser [(Pat Type QName)]
somePatterns
  = concat <$> someSI (Trifecta.try patternBinding <|> pure <$> atomicPattern)

manyPlicitPatterns :: Parser [(Plicitness, Pat Type QName)]
manyPlicitPatterns
  = concat <$> manySI (Trifecta.try plicitPatternBinding <|> pure <$> plicitPattern)

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
manyTypedBindings = concat <$> manySI (Trifecta.try typedBinding <|> plicitBinding')

-------------------------------------------------------------------------------
-- * Expressions
locatedExpr :: Parser Expr -> Parser Expr
locatedExpr p = go <$> Trifecta.spanned p
  where
    go (e Trifecta.:~ s) = SourceLoc (Trifecta.render s) e

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

branches :: Parser [(Pat Type QName, Expr)]
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

exprWithoutWhere :: Parser Expr
exprWithoutWhere
  = locatedExpr
  $ Unscoped.pis <$> Trifecta.try (somePlicitPatternBindings <*% symbol "->") <*>% exprWithoutWhere
  <|> Unscoped.apps <$> atomicExpr <*> manySI argument <**> arr
  <|> plicitPi Implicit <$ symbol "@" <*>% atomicExpr <*% symbol "->" <*>% exprWithoutWhere
  <?> "expression"
  where
    plicitPi p argType retType = Pi p (AnnoPat argType WildcardPat) retType

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
  = Extern C . fmap (either id $ ExternPart . Text.pack) <$ Trifecta.string "(C|" <*> go
  <?> "Extern C expression"
  where
    go = Trifecta.char '\\' *> escaped <*> go
      <|> (:) <$ Trifecta.char '$' <*> (Left <$> macroPart) <*> go
      <|> [] <$ symbol "|)"
      <|> consChar <$> Trifecta.anyChar <*> go
    macroPart
      = TargetMacroPart PointerAlignment <$ Trifecta.string "target:" <* Trifecta.string "pointerAlignment"
      <|> TypeMacroPart <$ Trifecta.string "type:" <*> atomicExpr
      <|> ExprMacroPart <$> atomicExpr
    consChar c (Right t : rest) = Right (c:t) : rest
    consChar c rest = Right [c] : rest
    consChars = foldr (\c -> (consChar c .)) id
    escaped
      = consChar <$> Trifecta.char '$'
      <|> consChars <$> Trifecta.string "|)"
      <|> (\c -> consChars ('\\' : [c])) <$> Trifecta.anyChar

-------------------------------------------------------------------------------
-- * Literals
literal :: Parser Expr
literal
  = Lit . Integer <$> integer
  <|> string <$> Trifecta.stringLiteral

literalPat :: Parser (Pat t n)
literalPat
  = LitPat . Integer <$> integer
  <|> stringPat <$> Trifecta.stringLiteral

-------------------------------------------------------------------------------
-- * Definitions
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
          *>% clause
    (mtyp, clauses)
      <- (,) . Just <$> typeSig <*> someSameCol namedClause
      <|> (,) Nothing <$> ((:) <$> clause <*> manySameCol namedClause)
    return (Unscoped.Definition n abstr (NonEmpty.fromList clauses) mtyp)
  where
    typeSig = symbol ":" *>% expr
    clause = Clause <$> (Vector.fromList <$> manyPlicitPatterns) <*% symbol "=" <*>% expr

dataDef :: Parser TopLevelDefinition
dataDef = TopLevelDataDefinition <$ reserved "type" <*>% name <*> manyTypedBindings <*>%
  (concat <$% reserved "where" <*> manyIndentedOrSameCol conDef
  <|> id <$% symbol "=" <*>% sepBySI adtConDef (symbol "|"))
  where
    conDef = constrDefs <$> ((:) <$> constructor <*> manySI constructor)
      <*% symbol ":" <*>% expr
    constrDefs cs t = [ConstrDef c t | c <- cs]
    adtConDef = ConstrDef <$> constructor <*> (adtConType <$> manySI atomicExpr)
    adtConType es = Unscoped.pis ((\e -> (Explicit, AnnoPat e WildcardPat)) <$> es) Wildcard

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
-- | A definition or type declaration on the top-level
modul :: Parser (Module [(SourceLoc, Unscoped.TopLevelDefinition)])
modul = Trifecta.whiteSpace >> dropAnchor
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
