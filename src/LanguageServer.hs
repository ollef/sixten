{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DisambiguateRecordFields #-}
module LanguageServer where

import Protolude hiding (state)

import Control.Concurrent.STM as STM
import Control.Lens hiding (unsnoc)
import Data.Default (def)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Map as Map
import Data.Text(Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Language.Haskell.LSP.Control as LSP
import qualified Language.Haskell.LSP.Core
import qualified Language.Haskell.LSP.Core as LSP
import qualified Language.Haskell.LSP.Diagnostics as LSP
import qualified Language.Haskell.LSP.Messages as LSP
import qualified Language.Haskell.LSP.Types as LSP
import qualified Language.Haskell.LSP.Types.Lens as LSP
import qualified Language.Haskell.LSP.VFS as LSP
import Text.Parsix.Position
import qualified Yi.Rope as Yi

import Driver
import Driver.Query
import qualified Effect.Context as Context
import Elaboration.TypeOf
import LanguageServer.Hover as Hover
import Syntax
import Util

run :: IO ()
run = do
  messageQueue <- newTQueueIO
  _ <- LSP.run
    ( \_ -> Right ()
    , \lf -> do
      _ <- forkIO $ messagePump lf $ atomically $ readTQueue messageQueue
      return Nothing
    )
    (handlers $ atomically . writeTQueue messageQueue)
    options
    Nothing -- (Just "sixten-lsp.log")
  return ()

handlers :: (LSP.FromClientMessage -> IO ()) -> LSP.Handlers
handlers sendMessage = def
  { LSP.initializedHandler = Just $ sendMessage . LSP.NotInitialized
  , LSP.hoverHandler = Just $ sendMessage . LSP.ReqHover
  , LSP.didOpenTextDocumentNotificationHandler = Just $ sendMessage . LSP.NotDidOpenTextDocument
  , LSP.didSaveTextDocumentNotificationHandler = Just $ sendMessage . LSP.NotDidSaveTextDocument
  , LSP.didChangeTextDocumentNotificationHandler = Just $ sendMessage . LSP.NotDidChangeTextDocument
  , LSP.didCloseTextDocumentNotificationHandler = Just $ sendMessage . LSP.NotDidCloseTextDocument
  }

options :: LSP.Options
options = def
  { Language.Haskell.LSP.Core.textDocumentSync = Just $ LSP.TextDocumentSyncOptions
    { LSP._openClose = Just True
    , LSP._change = Just LSP.TdSyncIncremental
    , LSP._willSave = Just False
    , LSP._willSaveWaitUntil = Just False
    , LSP._save = Just $ LSP.SaveOptions $ Just False
    }
  }

messagePump :: LSP.LspFuncs () -> IO LSP.FromClientMessage -> IO ()
messagePump lf receiveMessage = do
  state <- Driver.initialState
  forever $ do
    message <- receiveMessage
    case message of
      LSP.NotInitialized _ ->
        return ()

      LSP.NotDidOpenTextDocument notification -> do
        sendNotification lf "messagePump: processing NotDidOpenTextDocument"
        let
          document = notification ^. LSP.params . LSP.textDocument . LSP.uri
          version = notification ^. LSP.params . LSP.textDocument . LSP.version
          fileName = LSP.uriToFilePath document
        sendNotification lf $ "fileName = " <> show fileName
        sendDiagnostics lf state document $ Just version

      LSP.NotDidChangeTextDocument notification -> do
        let
          document = notification ^. LSP.params . LSP.textDocument . LSP.uri
          version = notification ^. LSP.params . LSP.textDocument . LSP.version

        sendNotification lf $ "messagePump:processing NotDidChangeTextDocument: uri=" <> show document
        sendDiagnostics lf state document version

      LSP.NotDidSaveTextDocument notification -> do
        sendNotification lf "messagePump: processing NotDidSaveTextDocument"
        let
          document = notification ^. LSP.params . LSP.textDocument . LSP.uri
          fileName = LSP.uriToFilePath document
        sendNotification lf $ "fileName = " <> show fileName
        sendDiagnostics lf state document Nothing

      LSP.ReqHover req -> do
        sendNotification lf $ "messagePump: HoverRequest: " <> show req
        let
          LSP.TextDocumentPositionParams
            (LSP.TextDocumentIdentifier document)
            pos@(LSP.Position line char)
              = req ^. LSP.params

        sendNotification lf $ shower document
        sendNotification lf $ shower pos
        (_version, contents) <- fileContents lf document
        let
          LSP.Uri uriText = document
          uriStr = Text.unpack uriText
        ((types, typeOfErrs), _) <- Driver.incrementallyExecuteVirtualFile state uriStr contents $ do
          defs <- fetch CheckAll
          runHover $ do
            (span, expr) <- hoverDefs (Hover.inside line char)
              [ (n, loc, d, t)
              | (n, (loc, d, t)) <- concatMap HashMap.toList defs
              ]
            typ <- typeOf' voidArgs expr
            ctx <- Context.getContext
            return (span, ctx, expr, typ)
        sendNotification lf $ "result " <> shower typeOfErrs
        let
          response = case types of
            [] -> Nothing
            _ -> do
              let Just (_, (range, ctx, expr, typ)) = unsnoc types
              Just $ LSP.Hover
                { LSP._contents =
                  LSP.List
                    [ LSP.PlainString
                      $ showWide
                      $ pretty (traverse Context.prettyVar expr ctx)
                      <> " : "
                      <> pretty (traverse Context.prettyVar typ ctx)
                    ]
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
        LSP.sendFunc lf $ LSP.RspHover $ LSP.makeResponseMessage req response

      _ ->
        return ()

-------------------------------------------------------------------------------
sendDiagnostics
  :: LSP.LspFuncs ()
  -> DriverState
  -> LSP.Uri
  -> LSP.TextDocumentVersion
  -> IO ()
sendDiagnostics lf state document version = do
  (currentVersion, contents) <- fileContents lf document
  case (version, currentVersion) of
    (Just v, Just cv)
      | v < cv ->
        return ()
    _ -> do
      let
        LSP.Uri uriText = document
        uriStr = Text.unpack uriText

      (_, errors) <- Driver.incrementallyExecuteVirtualFile state uriStr contents $ fetch CheckAll

      LSP.publishDiagnosticsFunc lf (length errors) document version
        $ LSP.partitionBySource $ errorToDiagnostic <$> errors

-------------------------------------------------------------------------------
sendNotification :: LSP.LspFuncs () -> Text -> IO ()
sendNotification lf s = LSP.sendFunc lf
  $ LSP.NotLogMessage
  $ LSP.NotificationMessage "2.0" LSP.WindowLogMessage
  $ LSP.LogMessageParams LSP.MtInfo s

diagnosticSource :: LSP.DiagnosticSource
diagnosticSource = "sixten"

sendError :: LSP.LspFuncs () -> LSP.Uri -> LSP.TextDocumentVersion -> Error -> IO ()
sendError lf uri version e =
  LSP.publishDiagnosticsFunc lf 10 uri version $
    Map.singleton (Just diagnosticSource) [errorToDiagnostic e]

errorToDiagnostic :: Error -> LSP.Diagnostic
errorToDiagnostic err = LSP.Diagnostic
  { _range = maybe
    (LSP.Range (LSP.Position 0 0) (LSP.Position 0 0))
    (spanToRange . sourceLocSpan)
    (errorLocation err)
  , _severity = Just LSP.DsError
  , _code = Nothing
  , _source = Just diagnosticSource
  , _message = showWide $ errorSummary err <> "\n" <> errorFootnote err
  , _relatedInformation = Nothing
  }

spanToRange :: Span -> LSP.Range
spanToRange span = LSP.Range
  { _start = positionToPosition $ spanStart span
  , _end = positionToPosition $ spanEnd span
  }

positionToPosition :: Position -> LSP.Position
positionToPosition pos = LSP.Position
  { _line = visualRow pos
  , _character = visualColumn pos
  }

fileContents :: LSP.LspFuncs () -> LSP.Uri -> IO (LSP.TextDocumentVersion, Text)
fileContents lf uri = do
  mvf <- LSP.getVirtualFileFunc lf uri
  case mvf of
    Just (LSP.VirtualFile version rope) -> return (Just version, Yi.toText rope)
    Nothing ->
      case LSP.uriToFilePath uri of
        Just fp ->
          (,) Nothing <$> Text.readFile fp
        Nothing ->
          return (Just 0, "")
