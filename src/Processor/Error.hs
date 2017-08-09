{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, OverloadedStrings #-}
module Processor.Error where

import Data.Monoid
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
      $ doc <> Leijen.linebreak
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
      $ doc <> Leijen.linebreak

data Result a
  = Error Error
  | Success a
  deriving (Show, Functor, Foldable, Traversable)
