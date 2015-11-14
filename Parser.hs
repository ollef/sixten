{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Parser where

import Bound
import Control.Applicative((<**>), (<|>), Alternative)
import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor
import Data.Text(Text)
import qualified Data.Text as Text
import Data.Char
import qualified Data.HashSet as HS
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Ord
import qualified Text.Parser.Token.Highlight as Highlight
import qualified Text.Trifecta as Trifecta
import Text.Trifecta((<?>))
import Text.Trifecta.Delta

import Annotation
import Branches
import Data
import Hint
import Input
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

instance Trifecta.TokenParsing Parser where
  someSpace = Trifecta.skipSome (Trifecta.satisfy isSpace) *> (comments <|> pure ())
           <|> comments
    where
      comments = (lineComment <|> multilineComment) *> Trifecta.whiteSpace

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
    res    = HS.fromList ["forall", "_", "Type", "case", "of", "where"]

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
literal = Trifecta.token Trifecta.integer

constructor :: Parser Constr
constructor = ident

data Binding
  = Plain Plicitness [Maybe Name]
  | Typed Plicitness [Maybe Name] (Expr Name)
  deriving (Eq, Ord, Show)

abstractBindings :: (NameHint -> Plicitness -> Maybe (Expr Name)
                              -> Scope1 Expr Name -> Expr Name)
                 -> [Binding]
                 -> Expr Name -> Expr Name
abstractBindings c = flip $ foldr f
  where
    f (Plain p xs)   e = foldr (\x -> c (h x) p Nothing  . abstractMaybe1 x) e xs
    f (Typed p xs t) e = foldr (\x -> c (h x) p (Just t) . abstractMaybe1 x) e xs
    abstractMaybe1 = maybe abstractNone abstract1
    h = Hint

bindingNames :: [Binding] -> Vector (Maybe Name)
bindingNames bs = Vector.fromList $ bs >>= flatten
  where
    flatten (Plain _ names) = names
    flatten (Typed _ names _) = names

abstractBindingTelescope :: [Binding] -> Vector (NameHint, Plicitness, Scope Int Expr Name)
abstractBindingTelescope bs
  = Vector.imap (\i (n, p, t) -> (Hint n, p, abstract (abstr i) t)) unabstracted
  where
    unabstracted = Vector.fromList $ bs >>= flatten
    abstr i v = case Vector.elemIndex (Just v) $ bindingNames bs of
      Just n | n < i -> Just n
      _ -> Nothing
    flatten (Plain p names) = [(name, p, Wildcard) | name <- names]
    flatten (Typed p names t) = [(name, p, t) | name <- names]

atomicBinding :: Parser Binding
atomicBinding
  =  Plain Explicit . (:[]) <$> identOrWildcard
 <|> Typed Explicit <$ symbol "(" <*>% someSI identOrWildcard <*% symbol ":" <*>% expr <*% symbol ")"
 <|> implicit <$ symbol "{" <*>% someSI identOrWildcard
              <*> Trifecta.optional (id <$% symbol ":" *> expr)
              <*% symbol "}"
 <?> "atomic variable binding"
 where
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
caseBinding = implicit <$ symbol "{" <*>% someSI identOrWildcard <*% symbol "}"
           <|> explicit <$> identOrWildcard
  where
    implicit xs = [(x, Implicit) | x <- xs]
    explicit x = [(x, Explicit)]

atomicExpr :: Parser (Expr Name)
atomicExpr
  =  Type     <$ reserved "Type"
 <|> Wildcard <$ wildcard
 <|> Var      <$> ident
 <|> abstr (reserved "forall") piType
 <|> abstr (symbol   "\\")     lam
 <|> Case <$ reserved "case" <*>% expr <*% reserved "of" <*>% dropAnchor branches
 <|> symbol "(" *>% expr <*% symbol ")"
 <?> "atomic expression"
  where
    abstr t c = abstractBindings c <$ t <*>% someBindings <*% symbol "." <*>% expr

branches :: Parser (Branches Expr Name)
branches = dropAnchor $  ConBranches <$> manySameCol conBranch
                     <|> LitBranches <$> manySameCol litBranch
                                     <*> (sameCol >> (reserved "_" *>% symbol "->" *>% expr))
  where
    litBranch = (,) <$> literal <*% symbol "->" <*>% expr
    conBranch = con <$> constructor <*> (concat <$> manySI caseBinding) <*% symbol "->" <*>% expr
    con c bs e = (c, vs, abstract ((`Vector.elemIndex` hs) . Just) e)
      where vs = Vector.fromList $ first Hint <$> bs
            hs = fst <$> Vector.fromList bs

expr :: Parser (Expr Name)
expr
  = (foldl (uncurry . App) <$> atomicExpr <*> manySI argument)
    <**> (typeAnno <|> arr Explicit <|> pure id)
 <|> ((symbol "{" *>% expr <*% symbol "}") <**> arr Implicit)
 <?> "expression"
  where
    typeAnno = flip Anno <$% symbol ":" <*>% expr
    arr p    = (\e' e -> Pi (Hint Nothing) p e $ Scope $ Var $ F e')
           <$% symbol "->" <*>% expr
    argument :: Parser (Plicitness, Expr Name)
    argument =  (,) Implicit <$ symbol "{" <*>% expr <*% symbol "}"
            <|> (,) Explicit <$> atomicExpr
            --
-- | A definition or type declaration on the top-level
data TopLevelParsed v
  = ParsedDefLine  (Maybe v) (Expr v) -- ^ Maybe v means that we can use wildcard names that refer e.g. to the previous top-level thing
  | ParsedTypeDecl v         (Type v)
  | ParsedData  v (DataDef Type v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

topLevel :: Parser (TopLevelParsed Name)
topLevel = dataDef <|> def

def :: Parser (TopLevelParsed Name)
def = ident    <**>% (typeDecl <|> mkDef Just)
  <|> wildcard <**>% mkDef (const Nothing)
  where
    typeDecl = flip ParsedTypeDecl <$ symbol ":" <*>% expr
    mkDef f = (\e n -> ParsedDefLine (f n) e) <$> (abstractBindings lam <$> manyBindings <*% symbol "=" <*>% expr)

dataDef :: Parser (TopLevelParsed Name)
dataDef = mkDataDef <$ reserved "data" <*>% constructor <*> manyBindings
    <*% reserved "where" <*> dropAnchor (manySameCol conDef)
  where
    conDef = ConstrDef <$> constructor <*% symbol ":" <*>% expr
    mkDataDef tc bindings cs = ParsedData tc
                             $ DataDef (abstractBindingTelescope bindings)
                                       (map abstrConstrDef cs)
      where
        abstrConstrDef (ConstrDef name typ)
          = ConstrDef name
          $ abstract ((`Vector.elemIndex` bindingNames bindings) . Just) typ

program :: Parser [TopLevelParsed Name]
program = Trifecta.whiteSpace >> dropAnchor (manySameCol $ dropAnchor topLevel)
