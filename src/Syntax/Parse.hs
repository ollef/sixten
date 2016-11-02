{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Syntax.Parse where

import Control.Applicative((<**>), (<|>), Alternative)
import Control.Monad.Except
import Control.Monad.State
import Data.Char
import qualified Data.HashSet as HS
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Text(Text)
import qualified Data.Text as Text
import Data.Ord
import qualified Text.Parser.Token.Highlight as Highlight
import qualified Text.Trifecta as Trifecta
import Text.Trifecta((<?>))
import Text.Trifecta.Delta

import Syntax
import Syntax.Concrete as Concrete
import Util

type Input = Text
newtype Parser a = Parser {runParser :: StateT Delta Trifecta.Parser a}
  deriving ( Monad, MonadPlus, MonadState Delta
           , Functor, Applicative, Alternative
           , Trifecta.Parsing, Trifecta.CharParsing
           , Trifecta.DeltaParsing
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
--
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

idStyle :: Trifecta.CharParsing m => Trifecta.IdentifierStyle m
idStyle = Trifecta.IdentifierStyle "Dependent" start letter res Highlight.Identifier Highlight.ReservedIdentifier
  where
    start  = Trifecta.satisfy isAlpha    <|> Trifecta.oneOf "_"
    letter = Trifecta.satisfy isAlphaNum <|> Trifecta.oneOf "_'"
    res    = HS.fromList ["forall", "_", "case", "of", "where"]

ident :: Parser Name
ident = Trifecta.token $ Trifecta.ident idStyle

reserved :: String -> Parser ()
reserved = Trifecta.token . Trifecta.reserve idStyle

wildcard :: Parser ()
wildcard = reserved "_"

identOrWildcard :: Parser (Maybe Name)
identOrWildcard = Just <$> ident
               <|> Nothing <$ wildcard

symbol :: String -> Parser Name
symbol = fmap Text.pack . Trifecta.token . Trifecta.symbol

literal :: Parser Literal
literal = Trifecta.token $ Trifecta.try Trifecta.integer

constructor :: Parser Constr
constructor = ident

data Binding
  = Plain Plicitness [Maybe Name]
  | Typed Plicitness [Maybe Name] (Expr Name)
  deriving (Eq, Show)

abstractBindings
  :: (NameHint -> Plicitness -> Maybe (Expr Name) -> Scope1 Expr Name -> Expr Name)
  -> [Binding]
  -> Expr Name -> Expr Name
abstractBindings c = flip $ foldr f
  where
    f (Plain p xs)   e = foldr (\x -> c (h x) p Nothing  . abstractMaybe1 x) e xs
    f (Typed p xs t) e = foldr (\x -> c (h x) p (Just t) . abstractMaybe1 x) e xs
    abstractMaybe1 = maybe abstractNone abstract1
    h = NameHint . Hint

bindingNames :: [Binding] -> Vector (Maybe Name)
bindingNames bs = Vector.fromList $ bs >>= flatten
  where
    flatten (Plain _ names) = names
    flatten (Typed _ names _) = names

bindingHints :: [Binding] -> Vector (NameHint, Plicitness)
bindingHints bs = Vector.fromList $ bs >>= flatten
  where
    flatten (Plain p names) = [(NameHint $ Hint n, p) | n <- names]
    flatten (Typed p names _type) = [(NameHint $ Hint n, p) | n <- names]

bindingsTelescope :: [Binding] -> Telescope Scope Plicitness Expr Name
bindingsTelescope bs = Telescope $
  Vector.imap (\i (n, p, t) -> (NameHint $ Hint n, p, abstract (abstr i) t)) unabstracted
  where
    unabstracted = Vector.fromList $ bs >>= flatten
    abstr i v = case Vector.elemIndex (Just v) $ bindingNames bs of
      Just n | n < i -> Just $ Tele n
      _ -> Nothing
    flatten (Plain p names) = [(name, p, Wildcard) | name <- names]
    flatten (Typed p names t) = [(name, p, t) | name <- names]

typedBinding :: Parser Binding
typedBinding
  = Typed Explicit <$ symbol "(" <*>% someSI identOrWildcard
    <*% symbol ":" <*>% expr <*% symbol ")"
  <|> Typed Implicit <$ symbol "{" <*>% someSI identOrWildcard
    <*% symbol ":" <*>% expr <*% symbol "}"
  <?> "typed variable binding"

someTypedBindings :: Parser [Binding]
someTypedBindings
  = someSI typedBinding
 <?> "typed variable bindings"

atomicBinding :: Parser Binding
atomicBinding
  = explicit <$> identOrWildcard
  <|> Typed Explicit <$ symbol "(" <*>% someSI identOrWildcard
    <*% symbol ":" <*>% expr <*% symbol ")"
  <|> implicit <$ symbol "{" <*>% someSI identOrWildcard
    <*> Trifecta.optional (id <$% symbol ":" *> expr)
    <*% symbol "}"
  <?> "atomic variable binding"
 where
  explicit x = Plain Explicit [x]
  implicit xs Nothing  = Plain Implicit xs
  implicit xs (Just t) = Typed Implicit xs t

someBindings :: Parser [Binding]
someBindings
  = someSI atomicBinding
 <?> "variable bindings"

manyBindings :: Parser [Binding]
manyBindings
  = manySI atomicBinding
 <?> "variable bindings"

caseBinding :: Parser [(Maybe Name, Plicitness)]
caseBinding
  = implicits <$ symbol "{" <*>% someSI identOrWildcard <*% symbol "}"
  <|> explicit <$> identOrWildcard
  where
    implicits xs = [(x, Implicit) | x <- xs]
    explicit x = [(x, Explicit)]

atomicExpr :: Parser (Expr Name)
atomicExpr
  = Lit <$> literal
 <|> Wildcard <$ wildcard
 <|> Var <$> ident
 <|> abstr (reserved "forall") piType
 <|> abstr (symbol   "\\")     Concrete.tlam
 <|> Case <$ reserved "case" <*>% expr <*% reserved "of" <*> branches
 <|> symbol "(" *>% expr <*% symbol ")"
 <?> "atomic expression"
  where
    abstr t c = abstractBindings c <$ t <*>% someBindings <*% symbol "." <*>% expr

branches :: Parser (Branches (Either Constr QConstr) Plicitness Expr Name)
branches
  = ConBranches <$> manyIndentedSameCol conBranch <*> pure Wildcard
 <|> LitBranches <$> manyIndentedSameCol litBranch
                 <*> (sameCol >> (reserved "_" *>% symbol "->" *>% expr))
  where
    litBranch = (,) <$> literal <*% symbol "->" <*>% expr
    conBranch = con <$> constructor <*> manyBindings <*% symbol "->" <*>% expr
    con c bs e = (Left c, bindingsTelescope bs, abstract (fmap Tele . (`Vector.elemIndex` ns) . Just) e)
      where
        ns = unNameHint . fst <$> bindingHints bs

expr :: Parser (Expr Name)
expr
  = abstractBindings piType <$> Trifecta.try someTypedBindings <*% symbol "->" <*>% expr
 <|> apps <$> atomicExpr <*> manySI argument
   <**> ((\f t -> f (Explicit, t)) <$> arr <|> pure id)
 <|> abstractBindings piType <$> funArgType <*% symbol "->" <*>% expr
 <?> "expression"
  where
    arr = (\e' (a, e) -> Pi mempty a e $ abstractNone e')
           <$% symbol "->" <*>% expr

    argument :: Parser (Plicitness, Expr Name)
    argument
      = (,) Implicit <$ symbol "{" <*>% expr <*% symbol "}"
      <|> (,) Explicit <$> atomicExpr

    funArgType :: Parser [Binding]
    funArgType
      = f Implicit <$ symbol "{" <*>% expr <*% symbol "}"
      <|> f Explicit <$> atomicExpr
      where
        f p t = [Typed p [Nothing] t]

-- | A definition or type declaration on the top-level
data TopLevelParsed v
  = ParsedDefLine (Maybe v) (Expr v) -- ^ Maybe v means that we can use wildcard names that refer e.g. to the previous top-level thing
  | ParsedTypeDecl v (Type v)
  | ParsedData v (Telescope Scope Plicitness Type v) (DataDef Type v)
  deriving (Eq, Foldable, Functor, Show, Traversable)

topLevel :: Parser (TopLevelParsed Name)
topLevel = dataDef <|> def

def :: Parser (TopLevelParsed Name)
def
  = ident <**>% (typeDecl <|> mkDef Just)
 <|> wildcard <**>% mkDef (const Nothing)
  where
    typeDecl = flip ParsedTypeDecl <$ symbol ":" <*>% expr
    mkDef f = (\e n -> ParsedDefLine (f n) e) <$> (abstractBindings Concrete.tlam <$> manyBindings <*% symbol "=" <*>% expr)

dataDef :: Parser (TopLevelParsed Name)
dataDef = mkDataDef <$ reserved "data" <*>% constructor <*> manyBindings
    <*% reserved "where" <*> manyIndentedSameCol conDef
  where
    conDef = ConstrDef <$> constructor <*% symbol ":" <*>% expr
    mkDataDef tc bs cs
      = ParsedData tc (bindingsTelescope bs) (DataDef $ map abstrConstrDef cs)
      where
        abstrConstrDef (ConstrDef name typ)
          = ConstrDef name
          $ abstract (fmap Tele . (`Vector.elemIndex` bindingNames bs) . Just) typ

program :: Parser [TopLevelParsed Name]
program = Trifecta.whiteSpace >> dropAnchor (manySameCol $ dropAnchor topLevel)
