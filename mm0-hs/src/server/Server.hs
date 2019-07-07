{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Server (server) where

import Control.Concurrent
import Control.Concurrent.STM.TChan
import qualified Control.Exception as E
import Control.Lens ((^.))
import Control.Monad.Reader
import Control.Monad.STM
import Data.Default
import Data.Maybe
import qualified Data.List.NonEmpty as NE (toList)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.ByteString.Lazy as BL
import qualified Language.Haskell.LSP.Control as Ctrl (run)
import Language.Haskell.LSP.Core
import Language.Haskell.LSP.Diagnostics
import Language.Haskell.LSP.Messages
import Language.Haskell.LSP.Types hiding (ParseError)
import qualified Language.Haskell.LSP.Types.Lens as J
import Language.Haskell.LSP.VFS
import System.Exit
import qualified System.Log.Logger as L
import Text.Megaparsec.Pos (SourcePos(..), unPos)
import qualified Text.Megaparsec.Error as E
import qualified Data.Rope.UTF16 as Rope
import qualified Parser as P
import qualified CParser as CP
import qualified Elaborator as Elab

server :: [String] -> IO ()
server ("--debug" : _) = atomically newTChan >>= run True
server _ = atomically newTChan >>= run False

catchAll :: forall a. IO a -> IO ()
catchAll m = () <$ (E.try m :: IO (Either E.SomeException a))

run :: Bool -> TChan FromClientMessage -> IO ()
run debug rin = do
  when debug $ catchAll $ setupLogger (Just "lsp.log") [] L.DEBUG
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

reactorSend :: FromServerMessage -> Reactor ()
reactorSend msg = do
  lf <- ask
  liftIO $ sendFunc lf msg

publishDiagnostics :: Int -> NormalizedUri -> TextDocumentVersion -> DiagnosticsBySource -> Reactor ()
publishDiagnostics maxToPublish uri v diags = do
  lf <- ask
  reactorLogs $ "publishDiagnostics " ++ show v ++ " " ++ show diags
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
        let TextDocumentItem uri _ version str = msg ^. J.params . J.textDocument
        sendDiagnostics (toNormalizedUri uri) (Just version) str

      -- -------------------------------

      NotDidChangeTextDocument msg -> do
        let VersionedTextDocumentIdentifier uri version = msg ^. J.params . J.textDocument
            doc = toNormalizedUri uri
        liftIO (getVirtualFileFunc lf doc) >>= \case
          Nothing -> reactorErr "reactor: Virtual File not found when processing DidChangeTextDocument"
          Just (VirtualFile _ str _) ->
            sendDiagnostics doc version (Rope.toText str)

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

mkDiagnostic :: Int -> Int -> String -> Diagnostic
mkDiagnostic l c msg =
  Diagnostic
    (Range (Position l c) (Position l c))
    (Just DsError)  -- severity
    Nothing  -- code
    (Just "MM0") -- source
    (T.pack msg)
    (Just (List []))

errorBundleDiags :: CP.ParseASTErrors -> [Diagnostic]
errorBundleDiags (E.ParseErrorBundle errs pos) =
  f <$> NE.toList (fst (E.attachSourcePos E.errorOffset errs pos)) where
  f (err, SourcePos _ l c) =
    mkDiagnostic (unPos l - 1) (unPos c - 1) (E.parseErrorTextPretty err)

-- | Analyze the file and send any diagnostics to the client in a
-- "textDocument/publishDiagnostics" msg
sendDiagnostics :: NormalizedUri -> Maybe Int -> T.Text -> Reactor ()
sendDiagnostics fileUri@(NormalizedUri t) version str = do
  let file = fromMaybe "" $ uriToFilePath $ fromNormalizedUri fileUri
  diags <- if False && T.isSuffixOf "mm0" t
    then case P.parse (BL.fromStrict (T.encodeUtf8 str)) of
      Left (P.ParseError l c msg) -> return [mkDiagnostic l c msg]
      Right ast -> case Elab.elabAST ast of
        Left msg -> return [mkDiagnostic 0 0 msg]
        Right _ -> return []
    else case CP.parseAST file str of
      Left (err, _) -> return (errorBundleDiags err)
      Right _ -> return []
  -- reactorSend $ NotificationMessage "2.0" "textDocument/publishDiagnostics" (Just r)
  publishDiagnostics 100 fileUri version (partitionBySource diags)
