{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Server (server) where

import           Control.Concurrent
import           Control.Concurrent.STM.TChan
import qualified Control.Exception                     as E
import           Control.Lens
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import           Control.Monad.STM
import qualified Data.Aeson                            as J
import           Data.Default
import qualified Data.HashMap.Strict                   as H
import qualified Data.Text                             as T
import qualified Language.Haskell.LSP.Control          as CTRL
import qualified Language.Haskell.LSP.Core             as Core
import           Language.Haskell.LSP.Diagnostics
import           Language.Haskell.LSP.Messages
import qualified Language.Haskell.LSP.Types            as J
import qualified Language.Haskell.LSP.Types.Lens       as J
import qualified Language.Haskell.LSP.Utility          as U
import           Language.Haskell.LSP.VFS
import           System.Exit
import qualified System.Log.Logger                     as L
import qualified Data.Rope.UTF16                       as Rope

server :: [String] -> IO ()
server _ = do
  rin <- atomically newTChan :: IO (TChan ReactorInput)

  let dp lf = do
        liftIO $ U.logs "main.run:dp entered"
        _rpid  <- forkIO $ reactor lf rin
        liftIO $ U.logs "main.run:dp tchan"
        -- dispatcherProc
        liftIO $ U.logs "main.run:dp after dispatcherProc"
        return Nothing

  Core.setupLogger (Just "lsp.log") [] L.DEBUG
  exitCode <- CTRL.run
    (Core.InitializeCallbacks (const (Right ())) (const (Right ())) dp)
    (lspHandlers rin)
    lspOptions
    Nothing -- (Just "lsp-session.log")
  exitWith (if exitCode == 0 then ExitSuccess else ExitFailure exitCode)

-- ---------------------------------------------------------------------

-- The reactor is a process that serialises and buffers all requests from the
-- LSP client, so they can be sent to the backend compiler one at a time, and a
-- reply sent.

data ReactorInput
  = HandlerRequest FromClientMessage
      -- ^ injected into the reactor input by each of the individual callback handlers

-- ---------------------------------------------------------------------

-- | The monad used in the reactor
type Reactor a = ReaderT (Core.LspFuncs ()) IO a

-- ---------------------------------------------------------------------
-- reactor monad functions
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------

reactorSend :: FromServerMessage -> Reactor ()
reactorSend msg = do
  lf <- ask
  liftIO $ Core.sendFunc lf msg

publishDiagnostics :: Int -> J.NormalizedUri -> J.TextDocumentVersion -> DiagnosticsBySource -> Reactor ()
publishDiagnostics maxToPublish uri v diags = do
  lf <- ask
  liftIO $ (Core.publishDiagnosticsFunc lf) maxToPublish uri v diags

nextLspReqId :: Reactor J.LspId
nextLspReqId = asks Core.getNextReqId >>= liftIO

reactorSendId :: (J.LspId -> FromServerMessage) -> Reactor ()
reactorSendId msg = nextLspReqId >>= reactorSend . msg

reactorLog :: T.Text -> Reactor ()
reactorLog msg = reactorSend $ NotLogMessage $ fmServerLogMessageNotification J.MtLog msg

-- ---------------------------------------------------------------------

-- | The single point that all events flow through, allowing management of state
-- to stitch replies and requests together from the two asynchronous sides: lsp
-- server and backend compiler
reactor :: Core.LspFuncs () -> TChan ReactorInput -> IO ()
reactor lf inp = do
  liftIO $ U.logs "reactor:entered"
  flip runReaderT lf $ forever $ do
    liftIO (atomically $ readTChan inp) >>= \case
      -- Handle any response from a message originating at the server, such as
      -- "workspace/applyEdit"
      HandlerRequest (RspFromClient rm) -> do
        liftIO $ U.logs $ "reactor:got RspFromClient:" ++ show rm

      -- -------------------------------

      HandlerRequest (NotInitialized _notification) -> do
        liftIO $ U.logm "****** reactor: processing Initialized Notification"
        let registrations = []
        reactorSendId $ \n -> ReqRegisterCapability $ fmServerRegisterCapabilityRequest n $
          J.RegistrationParams $ J.List registrations

      -- -------------------------------

      HandlerRequest (NotDidOpenTextDocument notification) -> do
        liftIO $ U.logm "****** reactor: processing NotDidOpenTextDocument"
        let
            doc  = notification ^. J.params
                                 . J.textDocument
                                 . J.uri
            fileName =  J.uriToFilePath doc
        liftIO $ U.logs $ "********* fileName=" ++ show fileName
        sendDiagnostics (J.toNormalizedUri doc) (Just 0)

      -- -------------------------------

      HandlerRequest (NotDidChangeTextDocument notification) -> do
        let doc :: J.NormalizedUri
            doc  = notification ^. J.params
                                 . J.textDocument
                                 . J.uri
                                 . to J.toNormalizedUri
        mdoc <- liftIO $ Core.getVirtualFileFunc lf doc
        case mdoc of
          Just (VirtualFile _version str _) -> do
            liftIO $ U.logs $ "reactor:processing NotDidChangeTextDocument: vf got:" ++ (show $ Rope.toString str)
          Nothing -> do
            liftIO $ U.logs "reactor:processing NotDidChangeTextDocument: vf returned Nothing"

        liftIO $ U.logs $ "reactor:processing NotDidChangeTextDocument: uri=" ++ (show doc)

      -- -------------------------------

      HandlerRequest (NotDidSaveTextDocument notification) -> do
        liftIO $ U.logm "****** reactor: processing NotDidSaveTextDocument"
        let
            doc  = notification ^. J.params
                                 . J.textDocument
                                 . J.uri
            fileName = J.uriToFilePath doc
        liftIO $ U.logs $ "********* fileName=" ++ show fileName
        sendDiagnostics (J.toNormalizedUri doc) Nothing

      -- -------------------------------

      HandlerRequest (ReqHover req) -> do
        liftIO $ U.logs $ "reactor:got HoverRequest:" ++ show req
        let J.TextDocumentPositionParams _doc pos = req ^. J.params
            J.Position _l _c' = pos

        let
          ht = Just $ J.Hover ms (Just range)
          ms = J.HoverContents $ J.markedUpContent "lsp-hello" "TYPE INFO"
          range = J.Range pos pos
        reactorSend $ RspHover $ Core.makeResponseMessage req ht

      -- -------------------------------

      HandlerRequest (ReqCodeAction req) -> do
        liftIO $ U.logs $ "reactor:got CodeActionRequest:" ++ show req
        let params = req ^. J.params
            doc = params ^. J.textDocument
            -- fileName = drop (length ("file://"::String)) doc
            -- J.Range from to = J._range (params :: J.CodeActionParams)
            (J.List diags) = params ^. J.context . J.diagnostics

        let
          -- makeCommand only generates commands for diagnostics whose source is us
          makeCommand (J.Diagnostic (J.Range start _) _s _c (Just "lsp-hello") _m _l) = [J.Command title cmd cmdparams]
            where
              title = "Apply LSP hello command:" <> head (T.lines _m)
              -- NOTE: the cmd needs to be registered via the InitializeResponse message. See lspOptions above
              cmd = "lsp-hello-command"
              -- need 'file' and 'start_pos'
              args = J.List
                      [ J.Object $ H.fromList [("file",     J.Object $ H.fromList [("textDocument",J.toJSON doc)])]
                      , J.Object $ H.fromList [("start_pos",J.Object $ H.fromList [("position",    J.toJSON start)])]
                      ]
              cmdparams = Just args
          makeCommand (J.Diagnostic _r _s _c _source _m _l) = []
        let body = J.List $ map J.CACommand $ concatMap makeCommand diags
            rsp = Core.makeResponseMessage req body
        reactorSend $ RspCodeAction rsp

      -- -------------------------------

      HandlerRequest om -> do
        liftIO $ U.logs $ "reactor:got HandlerRequest:" ++ show om

-- ---------------------------------------------------------------------

toWorkspaceEdit :: t -> Maybe J.ApplyWorkspaceEditParams
toWorkspaceEdit _ = Nothing

-- ---------------------------------------------------------------------

-- | Analyze the file and send any diagnostics to the client in a
-- "textDocument/publishDiagnostics" notification
sendDiagnostics :: J.NormalizedUri -> Maybe Int -> Reactor ()
sendDiagnostics fileUri version = do
  let diags = [
        J.Diagnostic
          (J.Range (J.Position 0 1) (J.Position 0 5))
          (Just J.DsWarning)  -- severity
          Nothing  -- code
          (Just "lsp-hello") -- source
          "Example diagnostic message"
          (Just (J.List []))]
  -- reactorSend $ J.NotificationMessage "2.0" "textDocument/publishDiagnostics" (Just r)
  publishDiagnostics 100 fileUri version (partitionBySource diags)

-- ---------------------------------------------------------------------

syncOptions :: J.TextDocumentSyncOptions
syncOptions = J.TextDocumentSyncOptions
  { J._openClose         = Just True
  , J._change            = Just J.TdSyncIncremental
  , J._willSave          = Just False
  , J._willSaveWaitUntil = Just False
  , J._save              = Just $ J.SaveOptions $ Just False
  }

lspOptions :: Core.Options
lspOptions = def { Core.textDocumentSync = Just syncOptions
                 , Core.executeCommandProvider = Just (J.ExecuteCommandOptions (J.List ["lsp-hello-command"]))
                 }

lspHandlers :: TChan ReactorInput -> Core.Handlers
lspHandlers rin
  = def { Core.initializedHandler                       = Just $ passHandler rin NotInitialized
        , Core.hoverHandler                             = Just $ passHandler rin ReqHover
        , Core.didOpenTextDocumentNotificationHandler   = Just $ passHandler rin NotDidOpenTextDocument
        , Core.didSaveTextDocumentNotificationHandler   = Just $ passHandler rin NotDidSaveTextDocument
        , Core.didChangeTextDocumentNotificationHandler = Just $ passHandler rin NotDidChangeTextDocument
        , Core.didCloseTextDocumentNotificationHandler  = Just $ passHandler rin NotDidCloseTextDocument
        , Core.cancelNotificationHandler                = Just $ passHandler rin NotCancelRequestFromClient
        , Core.responseHandler                          = Just $ responseHandlerCb rin
        , Core.codeActionHandler                        = Just $ passHandler rin ReqCodeAction
        }

-- ---------------------------------------------------------------------

passHandler :: TChan ReactorInput -> (a -> FromClientMessage) -> Core.Handler a
passHandler rin c notification =
  atomically $ writeTChan rin (HandlerRequest (c notification))

-- ---------------------------------------------------------------------

responseHandlerCb :: TChan ReactorInput -> Core.Handler J.BareResponseMessage
responseHandlerCb _rin resp = do
  U.logs $ "******** got ResponseMessage, ignoring:" ++ show resp

-- ---------------------------------------------------------------------
