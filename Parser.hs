module Parser where

import Bound
import Control.Applicative((<$>), (<$), (<*>), (<*), (*>))
import Control.Monad.State
import Data.Text(Text)
import qualified Data.Text as Text
import Data.Char
import Data.Ord
import Data.Set(Set)
import qualified Data.Set as S
import Text.Parsec hiding (State, token)
import Text.Parsec.Pos
import Text.Parsec.Text()

import Debug.Trace

import Input
import Util

type Input = Text
type Parser a = ParsecT Input () (State SourcePos) a

dbg s p = do
  st <- get
  pos <- getPosition
  res <- trace ("trying " ++ s ++ " " ++ show pos ++ " st: " ++ show st) p
  pos' <- getPosition
  trace (s ++ " " ++ show pos' ++ " = " ++ show res) $ return res

-- | Drop the indentation anchor -- use the current position as the reference
--   point in the given parser.
dropAnchor :: Parser a -> Parser a
dropAnchor p = do
  oldAnchor <- get
  pos       <- getPosition
  put pos
  result    <- p
  put oldAnchor
  return result

-- | Check that the current indentation level is the same as the anchor
sameCol :: Parser ()
sameCol = do
  pos    <- getPosition
  anchor <- get
  case comparing sourceColumn pos anchor of
    LT -> unexpected "unindent"
    EQ -> return ()
    GT -> unexpected "indent"

-- | Check that the current indentation level is on the same line as the anchor
--   or on a successive line but more indented.
sameLineOrIndented :: Parser ()
sameLineOrIndented = do
  pos    <- getPosition
  anchor <- get
  case (comparing sourceLine pos anchor, comparing sourceColumn pos anchor) of
    (EQ, _)  -> return () -- Same line
    (GT, GT) -> return () -- Indented
    (_,  _)  -> unexpected "unindent"

-- | One or more at the same indentation level.
many1SameCol :: Parser a -> Parser [a]
many1SameCol p = many1 (sameCol >> p)

-- | Zero or more at the same indentation level.
manySameCol :: Parser a -> Parser [a]
manySameCol p = many (sameCol >> p)

-- | One or more on the same line or a successive but indented line.
many1SI :: Parser a -> Parser [a]
many1SI p = many1 (sameLineOrIndented >> p)
--
-- | Zero or more on the same line or a successive but indented line.
manySI :: Parser a -> Parser [a]
manySI p = many (sameLineOrIndented >> p)

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

atoms :: Set Char
atoms = S.fromList ":=()\\."

isAtom  :: Char -> Bool
isAtom = (`S.member` atoms)

reserved :: Set Name
reserved = S.fromList
  [":", "=", "forall", ".", "_", "\\", "(", ")"]

isReserved  :: Name -> Bool
isReserved = flip S.member reserved

-- | Idents that parse as single tokens in expressions regardless of whitespace.
nonCompounds :: [Name]
nonCompounds = [","]

whitespace :: Parser ()
whitespace = skipMany space

whitespace1 :: Parser ()
whitespace1 = skipMany1 space

identLetter :: Parser Char
identLetter = satisfy $ \c -> not (isSpace c || isAtom c)

-- | Add whitespace after something.
token :: Parser a -> Parser a
token p = p <* whitespace

-- | Add mandatory whitespace after something.
token1 :: Parser a -> Parser a
token1 p = p <* whitespace1

-- | Reserved token.
rTok :: Name -> Parser Name
rTok = try . token1 . string

-- | Compound token.
cTok :: Name -> Parser Name
cTok = token . try . string

ident :: Parser Name
ident = token (try $ do
  s <- many1 (notFollowedBy nonCompoundIdent >> identLetter)
  if isReserved s
    then unexpected $ "reserved identifier " ++ show s
    else return s)
  <|> nonCompoundIdent
  <?> "identifier"
  where
    nonCompoundIdent = choice $ map cTok nonCompounds

defs :: Parser [Def Name]
defs = dropAnchor $ many1SameCol def

def :: Parser (Def Name)
def = Def <$> ident <*% rTok "=" <*>% expr

data Binding
  = Plain Name
  | Typed [Name] (Expr Name)
  deriving (Eq, Ord, Show)

abstractBindings :: [Binding] -> (Name -> Scope1 Expr Name -> Expr Name) -> Expr Name -> Expr Name
abstractBindings bs c = flip (foldr f) bs
  where
    f (Plain x) e    = c x $ abstract1 x e
    f (Typed xs t) e = foldr (\x -> c x . abstract1 x) e' xs
      where
        e' = e >>= \x -> if x `elem` xs then (return x `Anno` t) else return x

atomicBinding :: Parser Binding
atomicBinding
  =  Plain <$> ident
 <|> Typed <$ cTok "(" <*>% many1SI ident <*% cTok ":" <*>% expr <*% cTok ")"
 <?> "atomic variable binding"

bindings :: Parser [Binding]
bindings
  = many1SI atomicBinding
 <?> "variable bindings"

atomicExpr :: Parser (Expr Name)
atomicExpr
  =  Type <$ rTok "Type"
 <|> Wildcard <$ rTok "_"
 <|> Var  <$> ident
 <|> cTok "(" *>% expr <*% cTok ")"
 <?> "atomic expression"

expr :: Parser (Expr Name)
expr
  =  abstr (rTok "forall") Pi
 <|> abstr (cTok "\\") Lam
 <|> (foldl App <$> atomicExpr <*> many atomicExpr) 
     `followedBy` [anno, return]
 <?> "expression"
  where
    followedBy p ps = do
      x <- p
      choice $ map ($ x) ps

    anno e  = Anno e <$% cTok ":" <*>% expr

    abstr t c = do
      _ <- t
      sameLineOrIndented
      bs <- bindings
      sameLineOrIndented
      _ <- cTok "."
      sameLineOrIndented
      e <- expr
      return $ abstractBindings bs c e

test :: Parser a -> String -> Either ParseError a
test p s = evalState (runParserT (p <* eof) () "test" (Text.pack s)) (initialPos "test")
