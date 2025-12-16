{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant <$>" #-}
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
import qualified Data.Aeson as A
import qualified Data.HashMap.Strict as H
import qualified Data.Vector as V
import qualified Data.Vector.Mutable.Dynamic as VD
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Language.Haskell.LSP.Control as Ctrl (run)
import Language.Haskell.LSP.Core
import Language.Haskell.LSP.Diagnostics
import Language.Haskell.LSP.Messages
import Language.Haskell.LSP.Types
import qualified Language.Haskell.LSP.Types.Lens as J
import Language.Haskell.LSP.VFS
import Network.URI
import System.IO.Error
import System.Timeout
import System.Exit
import qualified System.Log.Logger as L
import qualified Data.Rope.UTF16 as Rope
import MM0.Compiler.PositionInfo
import qualified MM0.Compiler.AST as CA
import qualified MM0.Compiler.Parser as CP
import MM0.Compiler.PrettyPrinter hiding (doc)
import qualified MM0.Compiler.Env as CE
import qualified MM0.Compiler.Elaborator as CE
import MM0.Compiler.Elaborator (ErrorLevel(..))
import MM0.Util

server :: [String] -> IO ()
server ("--debug" : _) = atomically newTChan >>= run True
server _ = atomically newTChan >>= run False

catchAll :: forall a. IO a -> IO ()
catchAll m = void (E.try m :: IO (Either E.SomeException a))

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
    completionHandler                        = Just $ passHandler ReqCompletion,
    hoverHandler                             = Just $ passHandler ReqHover,
    definitionHandler                        = Just $ passHandler ReqDefinition,
    documentSymbolHandler                    = Just $ passHandler ReqDocumentSymbols,
    didOpenTextDocumentNotificationHandler   = Just $ passHandler NotDidOpenTextDocument,
    didChangeTextDocumentNotificationHandler = Just $ passHandler NotDidChangeTextDocument,
    didCloseTextDocumentNotificationHandler  = Just $ passHandler NotDidCloseTextDocument,
    didSaveTextDocumentNotificationHandler   = Just $ const $ return (),
    cancelNotificationHandler                = Just $ passHandler NotCancelRequestFromClient,
    responseHandler                          = Just $ passHandler RspFromClient,
    customNotificationHandler                = Just $ passHandler NotCustomClient }

  passHandler :: (a -> FromClientMessage) -> Handler a
  passHandler c msg = atomically $ writeTChan rin (c msg)


-- ---------------------------------------------------------------------

-- The reactor is a process that serialises and buffers all requests from the
-- LSP client, so they can be sent to the backend compiler one at a time, and a
-- reply sent.

data FileCache = FC {
  _fcText :: T.Text,
  _fcLines :: Lines,
  _fcAST :: CA.AST,
  _fcSpans :: V.Vector Spans,
  fcEnv :: CE.Env }

data ReactorState = RS {
  rsDebug :: Bool,
  rsFuncs :: LspFuncs (),
  rsDiagThreads :: TVar (H.HashMap NormalizedUri
    (TextDocumentVersion, Async (Either ResponseError FileCache))),
  rsLastParse :: TVar (H.HashMap NormalizedUri (TextDocumentVersion, FileCache)),
  rsOpenRequests :: TVar (H.HashMap LspId (BareResponseMessage -> IO ())) }
type Reactor a = ReaderT ReactorState IO a

-- ---------------------------------------------------------------------
-- reactor monad functions
-- ---------------------------------------------------------------------

reactorSend :: FromServerMessage -> Reactor ()
reactorSend msg = ReaderT $ \r -> sendFunc (rsFuncs r) msg

publishDiagnostics :: Int -> NormalizedUri -> TextDocumentVersion -> DiagnosticsBySource -> Reactor ()
publishDiagnostics maxToPublish uri v diags = ReaderT $ \r ->
  publishDiagnosticsFunc (rsFuncs r) maxToPublish uri v diags

nextLspReqId :: Reactor LspId
nextLspReqId = asks (getNextReqId . rsFuncs) >>= liftIO

asyncRec :: (Async a -> IO a) -> IO (Async a)
asyncRec f = do
  v <- newEmptyMVar
  a <- async $ takeMVar v >>= f
  a <$ putMVar v a

newDiagThread :: NormalizedUri -> TextDocumentVersion ->
  Reactor (Either ResponseError FileCache) ->
  Reactor (Async (Either ResponseError FileCache))
newDiagThread uri version m = ReaderT $ \rs -> do
  let dt = rsDiagThreads rs
  asyncRec $ \a -> do
    ao <- atomically $ H.lookup uri <$> readTVar dt >>= \case
      Just (v', a') | isOutdated v' version -> return $ Left a'
      a' -> Right (snd <$> a') <$ modifyTVar dt (H.insert uri (version, a))
    case ao of
      Left a' -> wait a'
      Right old -> do
        mapM_ cancel old
        -- enableAllocationLimit   -- TODO: Import following seems to exceed the alloc limit
        fromMaybe (Left $ ResponseError InternalError "server timeout" Nothing) <$>
          timeout (10 * 1000000) (runReaderT m rs)

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

isOutdated :: Maybe Int -> Maybe Int -> Bool
isOutdated (Just n) (Just v) = v <= n
isOutdated _ Nothing = True
isOutdated _ _ = False

traverseResponse :: Applicative f => (a -> f (Maybe b)) -> ResponseMessage a -> f (ResponseMessage b)
traverseResponse f (ResponseMessage j i r e) = flip (ResponseMessage j i) e . join <$> traverse f r

reactorReq :: A.FromJSON resp =>
  (RequestMessage ServerMethod req resp -> FromServerMessage) ->
  RequestMessage ServerMethod req resp ->
  (ResponseMessage resp -> Reactor ()) -> Reactor ()
reactorReq wrap msg resp = do
  r <- ask
  liftIO $ atomically $ modifyTVar (rsOpenRequests r) $ H.insert (msg ^. J.id) $
    \bresp -> case traverseResponse A.fromJSON bresp of
      A.Error err -> flip runReaderT r $
        reactorErr $ "mm0-hs: response parse error: " <> T.pack (show err)
      A.Success res -> do
        runReaderT (resp res) r
        liftIO $ atomically $ modifyTVar (rsOpenRequests r) $ H.delete (msg ^. J.id)
  reactorSend $ wrap msg

-- ---------------------------------------------------------------------

-- | The single point that all events flow through, allowing management of state
-- to stitch replies and requests together from the two asynchronous sides: lsp
-- server and backend compiler
reactor :: Bool -> LspFuncs () -> TChan FromClientMessage -> IO ()
reactor debug lf inp = do
  rs <- liftM3 (RS debug lf) (newTVarIO H.empty) (newTVarIO H.empty) (newTVarIO H.empty)
  flip runReaderT rs $ forever $ do
    liftIO (atomically $ readTChan inp) >>= \case
      -- Handle any response from a message originating at the server, such as
      -- "workspace/applyEdit"
      RspFromClient rm -> do
        reqs <- asks rsOpenRequests
        case rm ^. J.id of
          IdRspNull -> reactorErr $ "reactor:got null RspFromClient:" <> T.pack (show rm)
          lspid -> do
            liftIO (atomically $ H.lookup (requestId lspid) <$> readTVar reqs) >>= \case
              Nothing -> reactorErr $ "reactor:got response to unknown message:" <> T.pack (show rm)
              Just f -> liftIO $ f rm

      NotInitialized _ -> do
        let registrations = [
              Registration "mm0-hs-completion" TextDocumentCompletion Nothing]
        n <- nextLspReqId
        let msg = fmServerRegisterCapabilityRequest n $ RegistrationParams $ List registrations
        reactorReq ReqRegisterCapability msg $ const (return ())

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

      ReqCompletion req -> do
        let CompletionParams jdoc pos _ = req ^. J.params
        getCompletions (toNormalizedUri $ jdoc ^. J.uri) pos >>= reactorSend . \case
          Left err -> RspError $ makeResponseError (responseId $ req ^. J.id) err
          Right res -> RspCompletion $ makeResponseMessage req $ Completions $ List res

      ReqHover req -> do
        let TextDocumentPositionParams jdoc pos = req ^. J.params
            doc = toNormalizedUri $ jdoc ^. J.uri
        getFileCache doc >>= reactorSend . \case
          Left err -> RspError $ makeResponseError (responseId $ req ^. J.id) err
          Right (FC _ larr ast sps env) -> RspHover $ makeResponseMessage req $ do
            (stmt, CA.Span o pi') <- getPosInfo ast sps (toOffset larr pos)
            makeHover env (toRange larr o) stmt pi'

      ReqDefinition req -> do
        let TextDocumentPositionParams jdoc pos = req ^. J.params
            uri = jdoc ^. J.uri
        getFileCache (toNormalizedUri uri) >>= reactorSend . \case
          Left err -> RspError $ makeResponseError (responseId $ req ^. J.id) err
          Right (FC _ larr ast sps env) ->
            let {as = do
              (_, CA.Span _ pi') <- maybeToList $ getPosInfo ast sps (toOffset larr pos)
              goToDefinition larr env uri pi'}
            in RspDefinition $ makeResponseMessage req $ MultiLoc as

      ReqDocumentSymbols req -> do
        let doc = toNormalizedUri $ req ^. J.params . J.textDocument . J.uri
            fileUri = fromNormalizedUri doc
            file = fromMaybe "" $ uriToFilePath fileUri
        getFileCache doc >>= \case
          Left err -> reactorSend $ RspError $ makeResponseError (responseId $ req ^. J.id) err
          Right (FC _ larr _ _ env) -> liftIO (getSymbols larr file env) >>=
            reactorSend . RspDocumentSymbols . makeResponseMessage req . DSDocumentSymbols . List

      NotCustomClient (NotificationMessage _
        (CustomClientMethod "$/setTraceNotification") _) -> return ()

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

toOffset :: Lines -> Position -> Int
toOffset larr (Position l c) = posToOff larr l c

toPosition :: Lines -> Int -> Position
toPosition larr n = let (l, c) = offToPos larr n in Position l c

toRange :: Lines -> (Int, Int) -> Range
toRange larr (o1, o2) = Range (toPosition larr o1) (toPosition larr o2)

toLocation :: Lines -> (FilePath, (Int, Int)) -> Location
toLocation larr (p, r) = Location (filePathToUri p) (toRange larr r)

elabErrorDiags :: Lines -> [CE.ElabError] -> [Diagnostic]
elabErrorDiags larr = mapMaybe toDiag where
  toRel :: ((FilePath, (Int, Int)), T.Text) -> DiagnosticRelatedInformation
  toRel (loc, msg) = DiagnosticRelatedInformation (toLocation larr loc) msg
  toDiag :: CE.ElabError -> Maybe Diagnostic
  toDiag (CE.ElabError _ _ False _ _) = Nothing
  toDiag (CE.ElabError l (_, o) True msg es) =
    Just $ mkDiagnosticRelated l (toRange larr o) msg (toRel <$> es)

-- | Analyze the file and send any diagnostics to the client in a
-- "textDocument/publishDiagnostics" msg
elaborateFileAndSendDiags :: NormalizedUri ->
  TextDocumentVersion -> T.Text -> Reactor FileCache
elaborateFileAndSendDiags nuri@(NormalizedUri t) version str = do
  fs <- asks rsLastParse
  liftIO (readTVarIO fs) >>= \m -> case H.lookup nuri m of
    Just (oldv, fc) | isOutdated oldv version -> return fc
    _ -> do
      let fileUri = fromNormalizedUri nuri
          file = fromMaybe "" $ uriToFilePath fileUri
          larr = getLines str
          isMM0 = T.isSuffixOf "mm0" t
          (errs, _, ast) = CP.parseAST file str
      (errs', env) <- ReaderT $ \r ->
        CE.elaborate (mkElabConfig nuri isMM0 False r)
          (CE.toElabError def file <$> errs) ast
      let fc1 = FC str larr ast (toSpans env <$> ast) env
      fc <- liftIO $ atomically $ do
        h <- readTVar fs
        case H.lookup nuri h of
          Just (oldv, fc') | isOutdated oldv version -> return fc'
          _ -> fc1 <$ writeTVar fs (H.insert nuri (version, fc1) h)
      let diags = elabErrorDiags larr errs'
      publishDiagnostics 100 nuri version (partitionBySource diags)
      return fc

-- | Analyze the file and send any diagnostics to the client in a
-- "textDocument/publishDiagnostics" msg
sendDiagnostics :: NormalizedUri -> TextDocumentVersion -> T.Text -> Reactor ()
sendDiagnostics uri version str =
  reactorHandleAll $ (() <$) $ newDiagThread uri version $
    Right <$> elaborateFileAndSendDiags uri version str

getFileContents :: NormalizedUri -> Reactor (Either IOError T.Text)
getFileContents doc = do
  let fileUri = fromNormalizedUri doc
      file = fromMaybe "" $ uriToFilePath fileUri
  lf <- asks rsFuncs
  liftIO (getVirtualFileFunc lf doc) >>= \case
    Nothing -> lift $ E.try $ T.readFile file
    Just (VirtualFile _ rope _) -> return $ Right $ Rope.toText rope

getFileCache :: NormalizedUri -> Reactor (Either ResponseError FileCache)
getFileCache doc = do
  rs <- ask
  let lf = rsFuncs rs
  let dt = rsDiagThreads rs
  res <- liftIO (getVirtualFileFunc lf doc) >>= \case
    Nothing -> getFileContents doc <&> \case
      Left err -> Left (ResponseError InternalError
        (T.pack ("IO error: " ++ show err)) Nothing)
      Right str -> Right (Nothing, str)
    Just (VirtualFile version str _) ->
      return $ Right (Just version, Rope.toText str)
  case res of
    Left err -> return (Left err)
    Right (version, str) -> do
      a <- H.lookup doc <$> liftIO (readTVarIO dt) >>= \case
        Just (v', a') | isOutdated v' version -> return a'
        _ -> newDiagThread doc version $
          Right <$> elaborateFileAndSendDiags doc version str
      liftIO $ wait a

makeHover :: CE.Env -> Range -> CA.Span CA.Stmt -> PosInfo -> Maybe Hover
makeHover env range stmt (PosInfo t pi') = case pi' of
  PISort -> do
    (_, (_, _, (o, _)), sd) <- H.lookup t (CE.eSorts env)
    Just $ code $ ppStmt $ CA.Sort o t sd
  PIVar (Just bi) -> Just $ code $ ppBinder bi
  PIVar Nothing -> do
    CA.Span _ (CA.Decl _ _ _ st _ _ _) <- return stmt
    bis <- H.lookup st (CE.eDecls env) <&> \case
      (_, _, CE.DTerm bis _, _) -> bis
      (_, _, CE.DAxiom bis _ _, _) -> bis
      (_, _, CE.DDef _ bis _ _, _) -> bis
      (_, _, CE.DTheorem _ bis _ _ _, _) -> bis
    bi:_ <- return $ filter (\bi -> CE.binderName bi == t) bis
    Just $ code $ ppPBinder bi
  PITerm -> do
    (_, _, d, _) <- H.lookup t (CE.eDecls env)
    Just $ code $ ppDecl env t d
  PIAtom True (Just bi) -> Just $ code $ ppBinder bi
  PIAtom True Nothing -> do
    (_, _, d, _) <- H.lookup t (CE.eDecls env)
    Just $ code $ ppDecl env t d
  _ -> Nothing
  where

  hover ms = Hover (HoverContents ms) (Just range)
  code = hover . markedUpContent "mm0" . render'

relativeUri :: T.Text -> Uri -> Maybe Uri
relativeUri t (Uri uri) = do
  relUri <- parseURIReference $ T.unpack t
  absUri <- parseURI $ T.unpack uri
  return $ Uri $ T.pack $ show $ relUri `relativeTo` absUri

goToDefinition :: Lines -> CE.Env -> Uri -> PosInfo -> [Location]
goToDefinition larr env uri (PosInfo t pi') = case pi' of
  PISort -> maybeToList $
    H.lookup t (CE.eSorts env) <&> \(_, (p, _, rx), _) -> toLoc (p, rx)
  PIVar bi -> maybeToList $ binderLoc <$> bi
  PITerm -> maybeToList $
    H.lookup t (CE.eDecls env) <&> \(_, (p, _, rx), _, _) -> toLoc (p, rx)
  PIAtom b obi ->
    (case (b, obi) of
      (True, Just bi) -> [binderLoc bi]
      (True, Nothing) -> maybeToList $
        H.lookup t (CE.eDecls env) <&> \(_, (p, _, rx), _, _) -> toLoc (p, rx)
      _ -> []) ++
    maybeToList (
      H.lookup t (CE.eLispNames env) >>= fst <&> \(p, _, rx) -> toLoc (p, rx))
  PIFile -> traceShowId $ maybeToList $ flip Location (Range pos0 pos0) <$> relativeUri t uri
  where
  toLoc = toLocation larr
  binderLoc (CA.Binder o _ _) = Location uri (toRange larr o)
  pos0 = Position 0 0

getSymbols :: Lines -> FilePath -> CE.Env -> IO [DocumentSymbol]
getSymbols larr doc env = do
  let mkDS x det (p, rd, rx) sk = (p, DocumentSymbol x det sk Nothing
        (toRange larr rd) (toRange larr rx) Nothing)
  v <- VD.unsafeFreeze (CE.eLispData env)
  l1 <- flip mapMaybeM (H.toList (CE.eLispNames env)) $ \(x, (o, n)) -> do
    ty <- CE.unRefIO (v V.! n) <&> \case
      CE.Atom            {} -> Just SkConstant
      CE.List            {} -> Just SkArray
      CE.DottedList      {} -> Just SkObject
      CE.Number          {} -> Just SkNumber
      CE.String          {} -> Just SkString
      CE.UnparsedFormula {} -> Just SkString
      CE.Bool            {} -> Just SkBoolean
      CE.Syntax          {} -> Just SkEvent
      CE.Undef           {} -> Nothing
      CE.Proc            {} -> Just SkFunction
      CE.AtomMap         {} -> Just SkObject
      CE.Ref             {} -> undefined
      CE.MVar            {} -> Just SkConstant
      CE.Goal            {} -> Just SkConstant
    return $ liftM2 (mkDS x Nothing) o ty
  let l2 = H.toList (CE.eSorts env) <&> \(x, (_, r, _)) -> mkDS x Nothing r SkClass
  let l3 = H.toList (CE.eDecls env) <&> \(x, (_, r, d, _)) ->
        mkDS x (Just (renderNoBreak (ppDeclType env d))) r $ case d of
          CE.DTerm    {} -> SkConstructor
          CE.DDef     {} -> SkConstructor
          CE.DAxiom   {} -> SkMethod
          CE.DTheorem {} -> SkMethod
  return $ sortOn (\ds -> ds ^. J.selectionRange . J.start) $
    mapMaybe (\(p, ds) -> if p == doc then Just ds else Nothing) (l1 ++ l2 ++ l3)

getCompletions :: NormalizedUri -> Position ->
    Reactor (Either ResponseError [CompletionItem])
getCompletions doc@(NormalizedUri t) pos = do
  lf <- asks rsFuncs
  liftIO (getVirtualFileFunc lf doc) >>= \case
    Nothing -> return $ Left $ ResponseError InternalError "could not get file data" Nothing
    Just (VirtualFile version rope _) -> do
      let fileUri = fromNormalizedUri doc
          file = fromMaybe "" $ uriToFilePath fileUri
          str = Rope.toText rope
          larr = getLines str
          isMM0 = T.isSuffixOf "mm0" t
          publish = publishDiagnostics 100 doc (Just version) . partitionBySource
          (errs, _, ast) = CP.parseAST file str
      case markPosition (toOffset larr pos) ast of
        Nothing -> return $ Right []
        Just ast' -> do
          (errs', env) <- ReaderT $ \r ->
            CE.elaborate (mkElabConfig doc isMM0 True r)
              (CE.toElabError def file <$> errs) ast'
          fs <- asks rsLastParse
          liftIO $ atomically $ modifyTVar fs $ flip H.alter doc $ \case
            fc@(Just (oldv, _)) | isOutdated oldv (Just version) -> fc
            _ -> Just (Just version, FC str larr ast' (toSpans env <$> ast') env)
          publish (elabErrorDiags larr errs')
          ds <- liftIO $ getSymbols larr file env
          return $ Right $ ds <&> \(DocumentSymbol x det sk _ _ _ _) ->
            CompletionItem x (Just (toCIK sk)) det
              def def def def def def def def def def def def
  where
  toCIK :: SymbolKind -> CompletionItemKind
  toCIK SkMethod        = CiMethod
  toCIK SkFunction      = CiFunction
  toCIK SkConstructor   = CiConstructor
  toCIK SkField         = CiField
  toCIK SkVariable      = CiVariable
  toCIK SkClass         = CiClass
  toCIK SkInterface     = CiInterface
  toCIK SkModule        = CiModule
  toCIK SkProperty      = CiProperty
  toCIK SkEnum          = CiEnum
  toCIK SkFile          = CiFile
  toCIK SkEnumMember    = CiEnumMember
  toCIK SkConstant      = CiConstant
  toCIK SkStruct        = CiStruct
  toCIK SkEvent         = CiEvent
  toCIK SkOperator      = CiOperator
  toCIK SkTypeParameter = CiTypeParameter
  toCIK _               = CiValue

elabLoader :: FilePath -> Reactor (Either T.Text CE.Env)
elabLoader p =
  let uri' = toNormalizedUri (filePathToUri p) in
  -- if uri' `elem` (uri : ds) then
  --   return $ Left $ T.pack $ "import cycle detected: " ++ show (uri : ds)
  -- else if length ds >= 4 then
  --   return $ Left $ T.pack $ "import depth limit exceeded: " ++ show (uri' : uri : ds)
  -- else
  ReaderT $ \r ->
    tryIOError (runReaderT (getFileCache uri') r) <&> \case
      Left err -> Left $ T.pack $ "elabLoader failed: " ++ show err
      Right (Left err) -> Left $ T.pack $ show err
      Right (Right fc) -> Right $ fcEnv fc

mkElabConfig :: NormalizedUri -> Bool -> Bool -> ReactorState -> CE.ElabConfig
mkElabConfig uri mm0 c r = CE.ElabConfig mm0 True c
  (fromMaybe "" $ uriToFilePath $ fromNormalizedUri uri)
  (\t -> runReaderT (elabLoader t) r)
