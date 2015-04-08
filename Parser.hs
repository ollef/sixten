module Parser where

import Bound
import Control.Applicative((<|>))
import Control.Monad.State
import Data.Text(Text)
import Data.Char
import qualified Data.HashSet as HS
import Data.Ord
import qualified Text.Parser.Token.Highlight as Highlight
import qualified Text.Trifecta as Trifecta
import Text.Trifecta((<?>))
import Text.Trifecta.Delta

import Input
import Util

type Input = Text
type Parser a = StateT Delta Trifecta.Parser a

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

-- * Applicative style combinators for checking that the second argument parser
--   is on the same line or indented compared to the anchor.
infixl 4 <$>%, <$%, <*>%, <*%, *>%
(<$>%) :: (a -> b) -> Parser a -> Parser b
f <$>% p = f <$> (sameLineOrIndented >> p)
(<$%) :: a -> Parser b -> Parser a
f <$%  p = f <$  (sameLineOrIndented >> p)
(<*>%) :: Parser (a -> b) -> Parser a -> Parser b
p <*>% q = p <*> (sameLineOrIndented >> q)
(<*%) :: Parser a -> Parser b -> Parser a
p <*%  q = p <*  (sameLineOrIndented >> q)
(*>%) :: Parser a -> Parser b -> Parser b
p *>%  q = p *>  (sameLineOrIndented >> q)

idStyle :: Trifecta.CharParsing m => Trifecta.IdentifierStyle m
idStyle = Trifecta.IdentifierStyle "Dependent" start letter res Highlight.Identifier Highlight.ReservedIdentifier
  where
    start  = Trifecta.satisfy isAlpha    <|> Trifecta.oneOf "_"
    letter = Trifecta.satisfy isAlphaNum <|> Trifecta.oneOf "_'"
    res    = HS.fromList ["forall", "_", "Type"]

ident :: Parser Name
ident = Trifecta.ident idStyle

reserved :: String -> Parser ()
reserved = Trifecta.reserve idStyle

defs :: Parser [Def Name]
defs = dropAnchor $ someSameCol def

symbol :: String -> Parser Name
symbol = Trifecta.symbol

def :: Parser (Def Name)
def = Def <$> ident <*% symbol "=" <*>% expr

data Binding
  = Plain Plicitness [Name]
  | Typed Plicitness [Name] (Expr Name)
  deriving (Eq, Ord, Show)

abstractBindings :: [Binding]
                 -> (NameHint -> Plicitness -> Maybe (Expr Name)
                              -> Scope1 Expr Name -> Expr Name)
                 -> Expr Name -> Expr Name
abstractBindings bs c = flip (foldr f) bs
  where
    f (Plain p xs) e   = foldr (\x -> c (h x) p Nothing . abstract1 x) e xs
    f (Typed p xs t) e = foldr (\x -> c (h x) p (Just t) . abstract1 x) e xs
    h = Hint . Just

atomicBinding :: Parser Binding
atomicBinding
  =  Plain Explicit . (:[]) <$> bident
 <|> Typed Explicit <$ symbol "(" <*>% someSI bident <*% symbol ":" <*>% expr <*% symbol ")"
 <|> implicit <$ symbol "{" <*>% someSI bident
              <*> Trifecta.optional (id <$% symbol ":" *> expr)
              <*% symbol "}"
 <?> "atomic variable binding"
 where
  bident = ident <|> "_" <$ reserved "_"
  implicit xs Nothing  = Plain Implicit xs
  implicit xs (Just t) = Typed Implicit xs t

bindings :: Parser [Binding]
bindings
  = someSI atomicBinding
 <?> "variable bindings"

atomicExpr :: Parser (Expr Name)
atomicExpr
  =  Type     <$ reserved "Type"
 <|> Wildcard <$ reserved "_"
 <|> Var      <$> ident
 <|> symbol "(" *>% expr <*% symbol ")"
 <?> "atomic expression"

expr :: Parser (Expr Name)
expr
  =  (abstr (reserved "forall") Pi
 <|> abstr (symbol   "\\") lam
 <|> foldl (uncurry . App) <$> atomicExpr <*> manySI argument)
     `followedBy` [anno, arr Explicit, return]
 <|> ((symbol "{" *>% expr <*% symbol "}") `followedBy` [arr Implicit])
 <?> "expression"
  where
    lam x p Nothing  = Lam x p
    lam x p (Just t) = (`Anno` Pi x p (Just t) (Scope Wildcard)) . Lam x p
    followedBy p ps = do
      x <- p
      Trifecta.choice $ map ($ x) ps

    anno e  = Anno e <$% symbol ":" <*>% expr

    arr p e = (Pi (Hint Nothing) p (Just e) . Scope . Var . F)
           <$% symbol "->" <*>% expr

    abstr t c = flip abstractBindings c <$ t <*>% bindings <*% symbol "." <*>% expr

    argument :: Parser (Plicitness, Expr Name)
    argument =  (,) Implicit <$ symbol "{" <*>% expr <*% symbol "}"
            <|> (,) Explicit <$> atomicExpr

test :: Parser a -> String -> Trifecta.Result a
test p = Trifecta.parseString (evalStateT p mempty <* Trifecta.eof) mempty
