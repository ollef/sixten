{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DisambiguateRecordFields #-}
module Command.LanguageServer where

import Protolude hiding (handle)

import Options.Applicative

import qualified LanguageServer

optionsParserInfo :: ParserInfo ()
optionsParserInfo = info (pure ())
  $ fullDesc
  <> progDesc "Start a language server"
  <> header "sixten language-server"

command :: ParserInfo (IO ())
command = (\() -> LanguageServer.run) <$> optionsParserInfo
