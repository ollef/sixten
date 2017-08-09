{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, OverloadedStrings #-}
module Processor.Result where

import Control.Monad
import Data.Monoid as Monoid
import Data.Semigroup as Semigroup
import Data.Text(Text)
import qualified Data.Text.IO as Text
import System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen

data Error
  = SyntaxError Leijen.Doc
  | ResolveError Text
  | TypeError Text
  | CommandLineError Leijen.Doc
  deriving Show

printError :: Error -> IO ()
printError err = case err of
  SyntaxError doc -> do
    Text.putStrLn "Syntax error"
    Leijen.displayIO stdout
      $ Leijen.renderPretty 0.8 80
      $ doc Monoid.<> Leijen.linebreak
  ResolveError s -> do
    Text.putStrLn "Syntax error"
    Text.putStrLn s
  TypeError s -> do
    Text.putStrLn "Type error"
    Text.putStrLn s
  CommandLineError doc -> do
    Text.putStrLn "Command-line error"
    Leijen.displayIO stdout
      $ Leijen.renderPretty 0.8 80
      $ doc Monoid.<> Leijen.linebreak

data Result a
  = Failure [Error]
  | Success a
  deriving (Show, Functor, Foldable, Traversable)

instance Semigroup a => Semigroup (Result a) where
  Failure es1 <> Failure es2 = Failure $ es1 Semigroup.<> es2
  Failure es1 <> _ = Failure es1
  _ <> Failure es2 = Failure es2
  Success a <> Success b = Success (a Semigroup.<> b)

instance Applicative Result where
  pure = Success
  Failure errs1 <*> Failure errs2 = Failure $ errs1 ++ errs2
  r1 <*> r2 = ap r1 r2

instance Monad Result where
  return = Success
  Failure errs >>= _ = Failure errs
  Success a >>= f = f a
