{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Server (server) where

import Control.Concurrent
import Control.Concurrent.STM.TChan
import Control.Lens ((^.))
import Control.Monad.Reader
import Control.Monad.STM
import Data.Default
import qualified Data.Text as T
import qualified Language.Haskell.LSP.Control as Ctrl (run)
import Language.Haskell.LSP.Core
import Language.Haskell.LSP.Diagnostics
import Language.Haskell.LSP.Messages
import Language.Haskell.LSP.Types
import qualified Language.Haskell.LSP.Types.Lens as J
import Language.Haskell.LSP.VFS
import System.Exit
import qualified System.Log.Logger as L
import qualified Data.Rope.UTF16 as Rope

server :: [String] -> IO ()
server _ = atomically newTChan >>= run

run :: TChan FromClientMessage -> IO ()
run rin = do
  setupLogger (Just "lsp.log") [] L.DEBUG
  exitCode <- Ctrl.run
    (InitializeCallbacks (const (Right ())) (const (Right ())) $
      \lf -> forkIO (reactor lf rin) >> return Nothing)
    lspHandlers
    lspOptions
    Nothing -- (Just "lsp-session.log")
  exitWith (if exitCode == 0 then ExitSuccess else ExitFailure exitCode)
  where
  lspOptions :: Options
  lspOptions = def {
    textDocumentSync = Just $ TextDocumentSyncOptions {
      _openClose         = Just True,
      _change            = Just TdSyncIncremental,
      _willSave          = Just False,
      _willSaveWaitUntil = Just False,
      _save              = Just $ SaveOptions $ Just False },
    executeCommandProvider = Just $ ExecuteCommandOptions $ List [] }

  lspHandlers :: Handlers
  lspHandlers = def {
    initializedHandler                       = Just $ passHandler NotInitialized,
    -- hoverHandler                             = Just $ passHandler ReqHover,
    didOpenTextDocumentNotificationHandler   = Just $ passHandler NotDidOpenTextDocument,
    didChangeTextDocumentNotificationHandler = Just $ passHandler NotDidChangeTextDocument,
    didCloseTextDocumentNotificationHandler  = Just $ passHandler NotDidCloseTextDocument,
    cancelNotificationHandler                = Just $ passHandler NotCancelRequestFromClient,
    responseHandler                          = Just $ passHandler RspFromClient }

  passHandler :: (a -> FromClientMessage) -> Handler a
  passHandler c msg = atomically $ writeTChan rin (c msg)


-- ---------------------------------------------------------------------

-- The reactor is a process that serialises and buffers all requests from the
-- LSP client, so they can be sent to the backend compiler one at a time, and a
-- reply sent.

type Reactor a = ReaderT (LspFuncs ()) IO a

-- ---------------------------------------------------------------------
-- reactor monad functions
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------

reactorSend :: FromServerMessage -> Reactor ()
reactorSend msg = do
  lf <- ask
  liftIO $ sendFunc lf msg

publishDiagnostics :: Int -> NormalizedUri -> TextDocumentVersion -> DiagnosticsBySource -> Reactor ()
publishDiagnostics maxToPublish uri v diags = do
  lf <- ask
  liftIO $ (publishDiagnosticsFunc lf) maxToPublish uri v diags

nextLspReqId :: Reactor LspId
nextLspReqId = asks getNextReqId >>= liftIO

reactorSendId :: (LspId -> FromServerMessage) -> Reactor ()
reactorSendId msg = nextLspReqId >>= reactorSend . msg

reactorLogMsg :: MessageType -> T.Text -> Reactor ()
reactorLogMsg mt msg = reactorSend $ NotLogMessage $ fmServerLogMessageNotification mt msg

reactorErr :: T.Text -> Reactor ()
reactorErr = reactorLogMsg MtError

reactorLog :: T.Text -> Reactor ()
reactorLog = reactorLogMsg MtLog

reactorLogs :: String -> Reactor ()
reactorLogs = reactorLog . T.pack

-- ---------------------------------------------------------------------

-- | The single point that all events flow through, allowing management of state
-- to stitch replies and requests together from the two asynchronous sides: lsp
-- server and backend compiler
reactor :: LspFuncs () -> TChan FromClientMessage -> IO ()
reactor lf inp = do
  flip runReaderT lf $ forever $ do
    liftIO (atomically $ readTChan inp) >>= \case
      -- Handle any response from a message originating at the server, such as
      -- "workspace/applyEdit"
      RspFromClient rm -> do
        reactorLogs $ "reactor:got RspFromClient:" ++ show rm

      -- -------------------------------

      NotInitialized _ -> do
        let registrations = []
        reactorSendId $ \n -> ReqRegisterCapability $ fmServerRegisterCapabilityRequest n $
          RegistrationParams $ List registrations

      -- -------------------------------

      NotDidOpenTextDocument msg -> do
        reactorLogs $ "****** reactor: processing NotDidOpenTextDocument" ++ show msg
        let TextDocumentItem uri _ version str = msg ^. J.params . J.textDocument
        sendDiagnostics (toNormalizedUri uri) (Just version) str

      -- -------------------------------

      NotDidChangeTextDocument msg -> do
        let VersionedTextDocumentIdentifier uri version = msg ^. J.params . J.textDocument
            doc = toNormalizedUri uri
        liftIO (getVirtualFileFunc lf doc) >>= \case
          Nothing -> reactorErr "reactor: Virtual File not found when processing DidChangeTextDocument"
          Just (VirtualFile _ str _) -> do
            reactorLogs $ "reactor:processing NotDidChangeTextDocument: vf got:" ++ show (Rope.toString str)
            sendDiagnostics doc Nothing (Rope.toText str)

      -- -------------------------------

      -- ReqHover req -> do
      --   reactorLogs $ "reactor:got HoverRequest:" ++ show req
      --   let J.TextDocumentPositionParams _doc pos = req ^. J.params
      --       J.Position _l _c' = pos
      --       ht = Just $ J.Hover ms (Just range)
      --       ms = J.HoverContents $ J.markedUpContent "lsp-hello" "TYPE INFO"
      --       range = J.Range pos pos
      --   reactorSend $ RspHover $ makeResponseMessage req ht

      -- -------------------------------

      om -> reactorLogs $ "reactor: got HandlerRequest:" ++ show om

-- ---------------------------------------------------------------------

-- | Analyze the file and send any diagnostics to the client in a
-- "textDocument/publishDiagnostics" msg
sendDiagnostics :: NormalizedUri -> Maybe Int -> T.Text -> Reactor ()
sendDiagnostics fileUri version str = do
  let diags = [
        Diagnostic
          (Range (Position 0 1) (Position 0 5))
          (Just DsWarning)  -- severity
          Nothing  -- code
          (Just "lsp-hello") -- source
          "Example diagnostic message"
          (Just (List []))]
  -- reactorSend $ NotificationMessage "2.0" "textDocument/publishDiagnostics" (Just r)
  publishDiagnostics 100 fileUri version (partitionBySource diags)
