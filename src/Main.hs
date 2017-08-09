{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad
import Data.Monoid
import Options.Applicative

import qualified Command.Compile as Compile
import qualified Command.Run as Run
import qualified Command.Test as Test

optionsParser :: ParserInfo (IO ())
optionsParser = info (helper <*> commands)
  $ fullDesc
  <> progDesc "Sixten compiler"
  <> header "sixten"

commands :: Parser (IO ())
commands = subparser
  $ command "compile" Compile.command
  <> command "run" Run.command
  <> command "test" Test.command

main :: IO ()
main = join $ execParser optionsParser
