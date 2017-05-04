{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Frontend.Parse where

import Control.Applicative((<**>), (<|>), Alternative)
import Control.Monad.Except
import Control.Monad.State
import Data.Char
import qualified Data.HashSet as HashSet
import Data.Ord
import Data.Text(Text)
import qualified Data.Text as Text
import qualified Data.Vector as Vector
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
    ( Monad, MonadPlus, MonadState Delta , Functor, Applicative, Alternative
    , Trifecta.Parsing, Trifecta.CharParsing , Trifecta.DeltaParsing
    )

parseString :: Parser a -> String -> Trifecta.Result a
parseString p = Trifecta.parseString (evalStateT (runParser p) mempty <* Trifecta.eof) mempty

parseFromFile :: MonadIO m => Parser a -> FilePath -> m (Maybe a)
parseFromFile p = Trifecta.parseFromFile
                $ evalStateT (runParser p) mempty <* Trifecta.eof

parseFromFileEx :: MonadIO m => Parser a -> FilePath -> m (Trifecta.Result a)
parseFromFileEx p = Trifecta.parseFromFileEx
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
deltaLine Columns {}           = 0
deltaLine Tab {}               = 0
deltaLine (Lines l _ _ _)      = fromIntegral l + 1
deltaLine (Directed _ l _ _ _) = fromIntegral l + 1

deltaColumn :: Delta -> Int
deltaColumn pos = fromIntegral (column pos) + 1

-- | Drop the indentation anchor -- use the current position as the reference
--   point in the given parser.
dropAnchor :: Parser a -> Parser a
dropAnchor p = do
  oldAnchor <- get
  pos       <- Trifecta.position
  put pos
  result    <- p
  put oldAnchor
  return result

-- | Check that the current indentation level is the same as the anchor
sameCol :: Parser ()
sameCol = do
  pos    <- Trifecta.position
  anchor <- get
  case comparing deltaColumn pos anchor of
    LT -> Trifecta.unexpected "unindent"
    EQ -> return ()
    GT -> Trifecta.unexpected "indent"

-- | Check that the current indentation level is on the same line as the anchor
--   or on a successive line but more indented.
sameLineOrIndented :: Parser ()
sameLineOrIndented = do
  pos    <- Trifecta.position
  anchor <- get
  case (comparing deltaLine pos anchor, comparing deltaColumn pos anchor) of
    (EQ, _)  -> return () -- Same line
    (GT, GT) -> return () -- Indented
    (_,  _)  -> Trifecta.unexpected "unindent"

-- | One or more at the same indentation level.
someSameCol :: Parser a -> Parser [a]
someSameCol p = Trifecta.some (sameCol >> p)

-- | Zero or more at the same indentation level.
manySameCol :: Parser a -> Parser [a]
manySameCol p = Trifecta.many (sameCol >> p)

manyIndentedSameCol :: Parser a -> Parser [a]
manyIndentedSameCol p
  = Trifecta.option []
  $ sameLineOrIndented >> dropAnchor (someSameCol p)

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
f <$% p = f <$  (sameLineOrIndented >> p)
(<*>%) :: Parser (a -> b) -> Parser a -> Parser b
p <*>%q = p <*> (sameLineOrIndented >> q)
(<*%) :: Parser a -> Parser b -> Parser a
p <*% q = p <*  (sameLineOrIndented >> q)
(*>%) :: Parser a -> Parser b -> Parser b
p *>% q = p *>  (sameLineOrIndented >> q)
(<**>%) :: Parser a -> Parser (a -> b) -> Parser b
p <**>% q = p <**> (sameLineOrIndented >> q)

-------------------------------------------------------------------------------
-- * Tokens
idStyle :: Trifecta.CharParsing m => Trifecta.IdentifierStyle m
idStyle = Trifecta.IdentifierStyle "Dependent" start letter res Highlight.Identifier Highlight.ReservedIdentifier
  where
    start = Trifecta.satisfy isAlpha <|> Trifecta.oneOf "_"
    letter = Trifecta.satisfy isAlphaNum <|> Trifecta.oneOf "_'"
    res = HashSet.fromList ["forall", "_", "case", "of", "where"]

ident :: Parser Name
ident = Trifecta.ident idStyle

reserved :: String -> Parser ()
reserved = Trifecta.reserve idStyle

wildcard :: Parser ()
wildcard = reserved "_"

identOrWildcard :: Parser (Maybe Name)
identOrWildcard
  = Just <$> ident
  <|> Nothing <$ wildcard

symbol :: String -> Parser Name
symbol = fmap (Name . Text.pack) . Trifecta.symbol

integer :: Parser Integer
integer = Trifecta.try Trifecta.integer

constructor :: Parser Constr
constructor = nameToConstr <$> ident

-------------------------------------------------------------------------------
-- * Patterns
locatedPat :: Parser (Pat typ v) -> Parser (Pat typ v)
locatedPat p = (\(pat Trifecta.:~ s) -> PatLoc (Trifecta.render s) pat) <$> Trifecta.spanned p

pattern :: Parser (Pat (Type Name) Name)
pattern = locatedPat $
  ( Trifecta.try (ConPat <$> (Left <$> constructor) <*> (Vector.fromList <$> someSI plicitPattern))
    <|> atomicPattern
  ) <**>
  ( AnnoPat <$% symbol ":" <*> expr
    <|> pure id
  ) <?> "pattern"

plicitPattern :: Parser (Plicitness, Pat (Type Name) Name)
plicitPattern = (,) Implicit <$ symbol "{" <*>% pattern <*% symbol "}"
  <|> (,) Explicit <$> atomicPattern
  <?> "explicit or implicit pattern"

atomicPattern :: Parser (Pat (Type Name) Name)
atomicPattern = locatedPat
  $ symbol "(" *>% pattern <*% symbol ")"
  <|> (\v -> VarPat (NameHint $ Hint $ Just v) v) <$> ident
  <|> WildcardPat <$ wildcard
  <|> literalPat
  <?> "atomic pattern"

patternBinding :: Parser [(Plicitness, Pat (Type Name) Name)]
patternBinding
  = go Implicit <$ symbol "{" <*> someSI atomicPattern <*% symbol ":" <*>% expr <*% symbol "}"
  <|> go Explicit <$ symbol "(" <*> someSI atomicPattern <*% symbol ":" <*>% expr <*% symbol ")"
  <?> "typed pattern"
  where
    go p pats t = [(p, AnnoPat t pat) | pat <- pats]

somePatternBindings :: Parser [(Plicitness, Pat (Type Name) Name)]
somePatternBindings = concat <$> someSI patternBinding

somePatterns :: Parser [(Plicitness, Pat (Type Name) Name)]
somePatterns = concat <$> someSI (Trifecta.try patternBinding <|> pure <$> plicitPattern)

manyPatterns :: Parser [(Plicitness, Pat (Type Name) Name)]
manyPatterns = concat <$> manySI (Trifecta.try patternBinding <|> pure <$> plicitPattern)

plicitBinding :: Parser (Plicitness, Name)
plicitBinding
  = (,) Implicit <$ symbol "{" <*>% ident <*% symbol "}"
  <|> (,) Explicit <$> ident
  <?> "variable binding"

plicitBinding' :: Parser [(Plicitness, Name, Type Name)]
plicitBinding'
  = (\(p, n) -> [(p, n, Wildcard)])<$> plicitBinding

typedBinding :: Parser [(Plicitness, Name, Type Name)]
typedBinding = fmap flatten
  $ (,,) Implicit <$ symbol "{" <*> someSI ident <*% symbol ":" <*>% expr <*% symbol "}"
  <|> (,,) Explicit <$ symbol "(" <*> someSI ident <*% symbol ":" <*>% expr <*% symbol ")"
  <?> "typed variable binding"
  where
    flatten (p, names, t) = [(p, name, t) | name <- names]

manyTypedBindings :: Parser [(Plicitness, Name, Type Name)]
manyTypedBindings = concat <$> manySI (Trifecta.try typedBinding <|> plicitBinding')

-------------------------------------------------------------------------------
-- * Expressions
located :: Parser (Expr v) -> Parser (Expr v)
located p = (\(e Trifecta.:~ s) -> SourceLoc (Trifecta.render s) e) <$> Trifecta.spanned p

atomicExpr :: Parser (Expr Name)
atomicExpr = located
  $ literal
  <|> Wildcard <$ wildcard
  <|> Var <$> ident
  <|> abstr (reserved "forall") Unscoped.pis
  <|> abstr (symbol   "\\") Unscoped.lams
  <|> Case <$ reserved "case" <*>% expr <*% reserved "of" <*> branches
  -- <|> lett <$ reserved "let" <*>% manyIndentedSamecol def <*% reserved "in" <*> expr
  <|> ExternCode <$> externCExpr
  <|> symbol "(" *>% expr <*% symbol ")"
  <?> "atomic expression"
  where
    abstr t c = c <$ t <*>% somePatterns <*% symbol "." <*>% expr

branches :: Parser [(Pat (Type Name) Name, Expr Name)]
branches = manyIndentedSameCol branch
  where
    branch = (,) <$> pattern <*% symbol "->" <*>% expr

expr :: Parser (Expr Name)
expr = located
  $ Unscoped.pis <$> Trifecta.try (somePatternBindings <*% symbol "->") <*>% expr
  <|> plicitPi Implicit <$ symbol "{" <*>% expr <*% symbol "}" <*% symbol "->" <*>% expr
  <|> Unscoped.apps <$> atomicExpr <*> manySI argument <**> (arr <|> pure id)
  <?> "expression"
  where
    plicitPi p argType retType = Pi p (AnnoPat argType WildcardPat) retType

    arr = flip (plicitPi Explicit) <$% symbol "->" <*>% expr

    argument :: Parser (Plicitness, Expr Name)
    argument
      = (,) Implicit <$ symbol "{" <*>% expr <*% symbol "}"
      <|> (,) Explicit <$> atomicExpr

-------------------------------------------------------------------------------
-- * Extern C
externCExpr :: Parser (Extern (Expr Name))
externCExpr
  = Extern C . fmap (either id $ ExternPart . Text.pack) <$ Trifecta.string "(C|" <*> go
  <?> "Extern C expression"
  where
    go = Trifecta.char '\\' *> escaped <*> go
      <|> (:) <$ Trifecta.char '$' <*> (Left <$> macroPart) <*> go
      <|> [] <$ symbol "|)"
      <|> consChar <$> Trifecta.anyChar <*> go
    macroPart
      = TypeMacroPart <$ Trifecta.string "type:" <*> atomicExpr
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
literal :: Parser (Expr Name)
literal
  = Lit . Integer <$> integer
  <|> string <$> Trifecta.stringLiteral

literalPat :: Parser (Pat (Type Name) Name)
literalPat
  = LitPat . Integer <$> integer
  <|> stringPat <$> Trifecta.stringLiteral

-------------------------------------------------------------------------------
-- * Definitions
-- | A definition or type declaration on the top-level
data TopLevelParsed v
  = ParsedClause (Maybe v) (Unscoped.Clause v)
  | ParsedTypeDecl v (Type v)
  | ParsedData v [(Plicitness, v, Type v)] [ConstrDef (Type v)]
  deriving (Show)

topLevel :: Parser (TopLevelParsed Name, Span)
topLevel = (\(d Trifecta.:~ s) -> (d, s)) <$> Trifecta.spanned (dataDef <|> def)

def :: Parser (TopLevelParsed Name)
def
  = ident <**>% (typeDecl <|> mkDef Just)
  <|> wildcard <**>% mkDef (const Nothing)
  where
    typeDecl = flip ParsedTypeDecl <$ symbol ":" <*>% expr
    mkDef f = (\ps e n -> ParsedClause (f n) (Unscoped.Clause ps e)) <$> (Vector.fromList <$> manyPatterns) <*% symbol "=" <*>% expr

dataDef :: Parser (TopLevelParsed Name)
dataDef = ParsedData <$ reserved "type" <*>% ident <*> manyTypedBindings <*>%
  (concat <$% reserved "where" <*> manyIndentedSameCol conDef
  <|> id <$% symbol "=" <*>% sepBySI adtConDef (symbol "|"))
  where
    conDef = constrDefs <$> ((:) <$> constructor <*> manySI constructor)
      <*% symbol ":" <*>% expr
    constrDefs cs t = [ConstrDef c t | c <- cs]
    adtConDef = ConstrDef <$> constructor <*> (adtConType <$> manySI atomicExpr)
    adtConType es = Unscoped.pis ((\e -> (Explicit, AnnoPat e WildcardPat)) <$> es) Wildcard

program :: Parser [(TopLevelParsed Name, Span)]
program = Trifecta.whiteSpace >> dropAnchor (manySameCol $ dropAnchor topLevel)
