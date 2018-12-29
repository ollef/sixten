module Main where

import Protolude

import Options.Applicative

import Command

main :: IO ()
main = join $ execParser optionsParser
