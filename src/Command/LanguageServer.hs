{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
module Command.LanguageServer where

import Data.Monoid
import qualified Data.Text.IO as Text
import Options.Applicative
import System.IO
import Util

import qualified Backend.Target as Target
import Command.Check.Options
import Error
import qualified Processor.Files as Processor
import qualified Processor.Result as Processor

import Data.List.Split as Split

import Syntax.Concrete.Scoped (ProbePos(..))

import qualified Syntax.Concrete.Scoped as Scoped
import Language.Haskell.LSP.Constant as LSP
import Language.Haskell.LSP.Control as LSP
import Language.Haskell.LSP.Core as LSP
import Language.Haskell.LSP.Diagnostics as LSP
import Language.Haskell.LSP.Messages as LSP
import Language.Haskell.LSP.TH.ClientCapabilities as LSP
import Language.Haskell.LSP.TH.Constants as LSP
import Language.Haskell.LSP.TH.DataTypesJSON as LSP hiding (change)
import Language.Haskell.LSP.Utility as LSP
import Language.Haskell.LSP.VFS as LSP

import Control.Concurrent.STM as STM
import Control.Concurrent

import Data.Default (def)

import Data.Aeson (ToJSON)

import qualified System.IO as IO

import Data.Char as Char

import qualified Yi.Rope as Yi
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

type params ~> response = LSP.LspFuncs () -> params -> IO (Maybe response)
type Notified params = LSP.LspFuncs () -> params -> IO ()

sendNotification lf s =
  LSP.sendFunc lf
    (LSP.NotificationMessage "2.0" LSP.WindowLogMessage
      (LSP.LogMessageParams LSP.MtInfo (T.pack s)))

fileContents :: LSP.LspFuncs () -> LSP.Uri -> IO Text
fileContents lf uri = do
  mvf <- LSP.getVirtualFileFunc lf uri
  case mvf of
    Just (VirtualFile _ rope) -> return (Yi.toText rope)
    Nothing ->
      case uriToFilePath uri of
        Just fp -> T.readFile fp
        Nothing -> return "Command.LanguageServer.fileContents: file missing"

hover :: TextDocumentPositionParams ~> Hover
hover lf (TextDocumentPositionParams (TextDocumentIdentifier uri) (Position line char)) = do
  contents <- fileContents lf uri
  let Uri uri_text = uri
  let uri_str = T.unpack uri_text
  res <- Processor.vfsCheck (pure (uri_str, contents)) (ProbePos uri_str line char)
  return $ Just Hover {
    _contents=LSP.List [ LSP.PlainString msg | (_probe_pos,msg) <- traverse res ],
    _range=Nothing
  }

server :: IO ()
server = do
  lsp_funcs_ref <- STM.newTVarIO (Nothing :: Maybe (LSP.LspFuncs ()))

  let handle
        :: ToJSON response => params ~> response
        -> Maybe (LSP.Handler (LSP.RequestMessage method params response))
      handle h = Just $ \ (LSP.RequestMessage jsonrpc req_id _method params) -> do
        Just lf <- STM.readTVarIO lsp_funcs_ref
        mresponse <- h lf params
        case mresponse of
          Just response -> do
            LSP.sendFunc lf (LSP.ResponseMessage jsonrpc (LSP.responseId req_id) (Just response) Nothing)
          Nothing -> return ()

  let notified
        :: Notified params
        -> Maybe (LSP.Handler (LSP.NotificationMessage method params))
      notified h = Just $ \ (LSP.NotificationMessage jsonrpc _method params) -> do
        Just lf <- STM.readTVarIO lsp_funcs_ref
        h lf params

  LSP.run
    (\ _ -> Right (), \ lf -> STM.atomically (STM.writeTVar lsp_funcs_ref (Just lf)) >> return Nothing)
    (def {
      hoverHandler=handle hover
    })
    def
  return ()




optionsParserInfo :: ParserInfo ()
optionsParserInfo = info (pure ())
  $ fullDesc
  <> progDesc "Start a language server"
  <> header "sixten lsp"

command :: ParserInfo (IO ())
command = const server <$> optionsParserInfo

