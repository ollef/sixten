{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DisambiguateRecordFields #-}
module Command.LanguageServer where

import Protolude hiding (handle)

import Control.Concurrent.STM as STM
import Data.Default (def)
import qualified Data.HashMap.Lazy as HashMap
import Data.Text(Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Language.Haskell.LSP.Control as LSP
import qualified Language.Haskell.LSP.Core as LSP
import qualified Language.Haskell.LSP.Messages as LSP
import qualified Language.Haskell.LSP.Types as LSP
import qualified Language.Haskell.LSP.VFS as LSP
import Options.Applicative
import Text.Parsix.Position
import qualified Yi.Rope as Yi

import Command.LanguageServer.Hover
import Driver
import Driver.Query
import Elaboration.TypeOf
import Syntax
import Util

sendNotification :: LSP.LspFuncs () -> Text -> IO ()
sendNotification lf s = LSP.sendFunc lf
  $ LSP.NotLogMessage
  $ LSP.NotificationMessage "2.0" LSP.WindowLogMessage
  $ LSP.LogMessageParams LSP.MtInfo s

fileContents :: LSP.LspFuncs () -> LSP.Uri -> IO Text
fileContents lf uri = do
  mvf <- LSP.getVirtualFileFunc lf uri
  case mvf of
    Just (LSP.VirtualFile _ rope) -> return (Yi.toText rope)
    Nothing ->
      case LSP.uriToFilePath uri of
        Just fp -> Text.readFile fp
        Nothing -> return "Command.LanguageServer.fileContents: file missing"

hover :: LSP.LspFuncs () -> LSP.TextDocumentPositionParams -> IO (Maybe LSP.Hover)
hover lf (LSP.TextDocumentPositionParams (LSP.TextDocumentIdentifier uri) p@(LSP.Position line char)) = do
  sendNotification lf "Hovering!"
  sendNotification lf (shower uri)
  sendNotification lf (shower p)
  contents <- fileContents lf uri
  sendNotification lf "fileContents"
  let LSP.Uri uri_text = uri
  let uri_str = Text.unpack uri_text
  ((types, typeOfErrs), errs) <- Driver.executeVirtualFile uri_str contents $ do
    defs <- fetch CheckAll
    runHover $ do
      (span, expr) <- hoverDefs (inside line char)
        [ (n, loc, d, t)
        | (n, (loc, d, t)) <- concatMap HashMap.toList defs
        ]
      typ <- typeOf' voidArgs expr
      return (span, expr, typ)
  sendNotification lf ("result " <> shower (typeOfErrs <> errs))
  sendNotification lf ("success " <> shower types)
  return $ case types of
    [] -> Nothing
    _ -> do
      let Just (_, (range, expr, typ)) = unsnoc types
      Just $ LSP.Hover
        { LSP._contents = LSP.List [LSP.PlainString $ showWide $ pretty (pretty <$> expr) <> " : " <> pretty (pretty <$> typ)]
        , LSP._range = Just
          $ LSP.Range
          { LSP._start = LSP.Position
            (visualRow $ spanStart range)
            (visualColumn $ spanStart range)
          , LSP._end = LSP.Position
            (visualRow $ spanEnd range)
            (visualColumn $ spanEnd range)
          }
        }

handle
  :: TVar (Maybe (LSP.LspFuncs ()))
  -> (LSP.LspFuncs () -> t -> IO resp)
  -> (LSP.ResponseMessage resp -> LSP.FromServerMessage)
  -> Maybe (LSP.RequestMessage m t resp -> IO ())
handle lspFuncsRef h rspCon = Just $ \(LSP.RequestMessage jsonRpc reqId _method params) -> do
  Just lf <- STM.readTVarIO lspFuncsRef
  response <- h lf params
  LSP.sendFunc lf
    $ rspCon
    $ LSP.ResponseMessage
      jsonRpc
      (LSP.responseId reqId)
      (Just response)
      Nothing

server :: IO ()
server = do
  lspFuncsRef <- STM.newTVarIO (Nothing :: Maybe (LSP.LspFuncs ()))

  _exitCode <- LSP.run
    ( \_ -> Right ()
    , \lf -> do
      STM.atomically $ STM.writeTVar lspFuncsRef $ Just lf
      return Nothing
    )
    def
      { LSP.hoverHandler = handle lspFuncsRef hover LSP.RspHover
      }
    def
    (Just "sixten-lsp.log")
  return ()

optionsParserInfo :: ParserInfo ()
optionsParserInfo = info (pure ())
  $ fullDesc
  <> progDesc "Start a language server"
  <> header "sixten lsp"

command :: ParserInfo (IO ())
command = (\() -> server) <$> optionsParserInfo
