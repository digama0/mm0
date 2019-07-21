{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
module MM0.Server (server) where

import Control.Concurrent
import Control.Concurrent.Async
import Control.Concurrent.STM
import qualified Control.Exception as E
import Control.Lens ((^.))
import Control.Monad.Reader
import Data.Default
import Data.List
import Data.Maybe
import qualified Data.IntMap as I
import qualified Data.HashMap.Strict as H
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
import qualified MM0.FrontEnd.Parser as P
import qualified MM0.Compiler.Parser as CP
import qualified MM0.FrontEnd.Elaborator as Elab
import qualified MM0.Compiler.Elaborator as CE
import MM0.Compiler.Elaborator (ErrorLevel(..))

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
      \lf -> forkIO (reactor debug lf rin) >> return Nothing)
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
    didSaveTextDocumentNotificationHandler   = Just $ const $ return (),
    cancelNotificationHandler                = Just $ passHandler NotCancelRequestFromClient,
    responseHandler                          = Just $ passHandler RspFromClient }

  passHandler :: (a -> FromClientMessage) -> Handler a
  passHandler c msg = atomically $ writeTChan rin (c msg)


-- ---------------------------------------------------------------------

-- The reactor is a process that serialises and buffers all requests from the
-- LSP client, so they can be sent to the backend compiler one at a time, and a
-- reply sent.

data ReactorState = RS {
  rsDebug :: Bool,
  rsFuncs :: LspFuncs (),
  rsDiagThreads :: TVar (H.HashMap (Maybe Int) (Async ())) }
type Reactor a = ReaderT ReactorState IO a

-- ---------------------------------------------------------------------
-- reactor monad functions
-- ---------------------------------------------------------------------

reactorSend :: FromServerMessage -> Reactor ()
reactorSend msg = do
  lf <- asks rsFuncs
  liftIO $ sendFunc lf msg

publishDiagnostics :: Int -> NormalizedUri -> TextDocumentVersion -> DiagnosticsBySource -> Reactor ()
publishDiagnostics maxToPublish uri v diags = do
  lf <- asks rsFuncs
  liftIO $ (publishDiagnosticsFunc lf) maxToPublish uri v diags

nextLspReqId :: Reactor LspId
nextLspReqId = asks (getNextReqId . rsFuncs) >>= liftIO

newDiagThread :: Maybe Int -> Reactor () -> Reactor ()
newDiagThread version m = ReaderT $ \rs -> do
  let dt = rsDiagThreads rs
  a <- async $ do
    runReaderT m rs
    as <- atomically $ do
      as <- readTVar dt
      let as' = H.delete version as
      as' <$ writeTVar dt as'
    forM_ version $ \v -> forM_ (H.toList as) $ \case
      (Just v', a) | v' < v -> cancel a
      _ -> return ()
  old <- atomically $ do
    as <- readTVar dt
    writeTVar dt (H.insert version a as)
    return (H.lookup version as)
  mapM_ cancel old

reactorSendId :: (LspId -> FromServerMessage) -> Reactor ()
reactorSendId msg = nextLspReqId >>= reactorSend . msg

reactorLogMsg :: MessageType -> T.Text -> Reactor ()
reactorLogMsg mt msg = reactorSend $ NotLogMessage $ fmServerLogMessageNotification mt msg

reactorErr :: T.Text -> Reactor ()
reactorErr = reactorLogMsg MtError

reactorLog :: T.Text -> Reactor ()
reactorLog s = do
  debug <- asks rsDebug
  when debug (reactorLogMsg MtLog s)

reactorLogs :: String -> Reactor ()
reactorLogs = reactorLog . T.pack

reactorHandle :: E.Exception e => (e -> Reactor ()) -> Reactor () -> Reactor ()
reactorHandle h m = ReaderT $ \lf ->
  E.handle (\e -> runReaderT (h e) lf) (runReaderT m lf)

reactorHandleAll :: Reactor () -> Reactor ()
reactorHandleAll = reactorHandle $ \(e :: E.SomeException) ->
  reactorErr $ T.pack $ E.displayException e

-- ---------------------------------------------------------------------

-- | The single point that all events flow through, allowing management of state
-- to stitch replies and requests together from the two asynchronous sides: lsp
-- server and backend compiler
reactor :: Bool -> LspFuncs () -> TChan FromClientMessage -> IO ()
reactor debug lf inp = do
  th <- atomically $ newTVar H.empty
  flip runReaderT (RS debug lf th) $ forever $ do
    liftIO (atomically $ readTChan inp) >>= \case
      -- Handle any response from a message originating at the server, such as
      -- "workspace/applyEdit"
      RspFromClient rm -> do
        reactorLogs $ "reactor:got RspFromClient:" ++ show rm

      NotInitialized _ -> do
        let registrations = []
        reactorSendId $ \n -> ReqRegisterCapability $ fmServerRegisterCapabilityRequest n $
          RegistrationParams $ List registrations

      NotDidOpenTextDocument msg -> do
        let TextDocumentItem uri _ version str = msg ^. J.params . J.textDocument
        sendDiagnostics (toNormalizedUri uri) (Just version) str

      NotDidChangeTextDocument msg -> do
        let VersionedTextDocumentIdentifier uri version = msg ^. J.params . J.textDocument
            doc = toNormalizedUri uri
        liftIO (getVirtualFileFunc lf doc) >>= \case
          Nothing -> reactorErr "reactor: Virtual File not found when processing DidChangeTextDocument"
          Just (VirtualFile _ str _) ->
            sendDiagnostics doc version (Rope.toText str)

      NotCancelRequestFromClient msg -> do
        reactorLogs $ "reactor:got NotCancelRequestFromClient:" ++ show msg

      -- ReqHover req -> do
      --   reactorLogs $ "reactor:got HoverRequest:" ++ show req
      --   let J.TextDocumentPositionParams _doc pos = req ^. J.params
      --       J.Position _l _c' = pos
      --       ht = Just $ J.Hover ms (Just range)
      --       ms = J.HoverContents $ J.markedUpContent "lsp-hello" "TYPE INFO"
      --       range = J.Range pos pos
      --   reactorSend $ RspHover $ makeResponseMessage req ht

      om -> reactorLogs $ "reactor: got HandlerRequest:" ++ show om

-- ---------------------------------------------------------------------

elSeverity :: ErrorLevel -> DiagnosticSeverity
elSeverity ELError = DsError
elSeverity ELWarning = DsWarning
elSeverity ELInfo = DsInfo

mkDiagnosticRelated :: ErrorLevel -> Range -> T.Text ->
  [DiagnosticRelatedInformation] -> Diagnostic
mkDiagnosticRelated l r msg rel =
  Diagnostic
    r
    (Just (elSeverity l))  -- severity
    Nothing  -- code
    (Just "MM0") -- source
    msg
    (Just (List rel))

mkDiagnostic :: Position -> T.Text -> Diagnostic
mkDiagnostic p msg = mkDiagnosticRelated ELError (Range p p) msg []

parseErrorDiags :: CP.PosState T.Text ->
  [CP.ParseError] -> [Diagnostic]
parseErrorDiags pos errs =
  toDiag <$> fst (E.attachSourcePos E.errorOffset errs' pos) where
  errs' = sortOn E.errorOffset errs
  toDiag (err, SourcePos _ l c) =
    mkDiagnostic (Position (unPos l - 1) (unPos c - 1))
      (T.pack (E.parseErrorTextPretty err))

elabErrorDiags :: Uri -> CP.PosState T.Text -> [CE.ElabError] -> [Diagnostic]
elabErrorDiags uri pos errs = toDiag <$> errs where
  offs :: I.IntMap Int
  offs = foldl'
    (\m (CE.ElabError _ o1 o2 _ es) ->
      I.insert o1 o1 $ I.insert o2 o2 $
      foldl' (\m' (o1', o2', _) -> I.insert o1' o1' $ I.insert o2' o2' m') m es)
    I.empty errs
  poss :: I.IntMap (Int, SourcePos)
  poss = fst $ E.attachSourcePos id offs pos
  toPosition :: Int -> Position
  toPosition n =
    let SourcePos _ l c = snd (poss I.! n) in
    Position (unPos l - 1) (unPos c - 1)
  toRange :: Int -> Int -> Range
  toRange o1 o2 = Range (toPosition o1) (toPosition o2)
  toRel :: (Int, Int, T.Text) -> DiagnosticRelatedInformation
  toRel (o1, o2, msg) = DiagnosticRelatedInformation
    (Location uri (toRange o1 o2)) msg
  toDiag :: CE.ElabError -> Diagnostic
  toDiag (CE.ElabError l o1 o2 msg es) =
    mkDiagnosticRelated l (toRange o1 o2) msg (toRel <$> es)

-- | Analyze the file and send any diagnostics to the client in a
-- "textDocument/publishDiagnostics" msg
sendDiagnostics :: NormalizedUri -> Maybe Int -> T.Text -> Reactor ()
sendDiagnostics fileNUri@(NormalizedUri t) version str =
  reactorHandleAll $ newDiagThread version $ do
    let fileUri = fromNormalizedUri fileNUri
        file = fromMaybe "" $ uriToFilePath fileUri
        pos = CP.initialPosState file str
    diags <- if T.isSuffixOf "mm0" t
      then case P.parse (BL.fromStrict (T.encodeUtf8 str)) of
        Left (P.ParseError l c msg) ->
          return [mkDiagnostic (Position l c) (T.pack msg)]
        Right ast -> case Elab.elabAST ast of
          Left msg -> return [mkDiagnostic (Position 0 0) (T.pack msg)]
          Right _ -> return []
      else case CP.parseAST file str of
        (errs, _, Nothing) -> return $ parseErrorDiags pos errs
        (errs, _, Just ast) -> do
          errs' <- liftIO $ CE.elaborate errs ast
          return (elabErrorDiags fileUri pos errs')
    publishDiagnostics 100 fileNUri version (partitionBySource diags)
