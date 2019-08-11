module MM0.Compiler.Export where

import Control.Monad.State
import Control.Monad.RWS.Strict
import Data.Bits
import Data.Default
import Data.IORef
import Data.Maybe
import Data.Word
import System.IO
import System.Exit
import qualified Data.Map.Strict as M
import qualified Data.HashMap.Strict as H
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.Binary.Builder as BB
import qualified Data.Vector as V
import qualified Data.Vector.Mutable.Dynamic as VD
import qualified Data.Text as T
import MM0.Compiler.Env hiding (reportErr)
import MM0.Util

export :: String -> Env -> IO ()
export fname env = do
  m <- collectDecls env
  t <- liftIO $ buildTables env m
  withBinaryFile fname WriteMode $ \h -> do
    hSetBuffering h (BlockBuffering Nothing)
    putExportM h (writeMM0B t m)

reportErr :: Range -> T.Text -> IO ()
reportErr _ = hPutStrLn stderr . T.unpack

isPublic :: Decl -> Bool
isPublic (DTerm _ _) = True
isPublic (DAxiom _ _ _) = True
isPublic (DDef vis _ _ _) = vis /= Local
isPublic (DTheorem vis _ _ _ _) = vis == Public

type DeclMap = M.Map SeqNum (Either Sort Ident)
collectDecls :: Env -> IO [Either Sort Ident]
collectDecls env = do
  m <- processDecls (H.toList (eDecls env)) M.empty
  return $ M.elems $ H.foldlWithKey' (\m' x (s, _, _) -> M.insert s (Left x) m') m (eSorts env)
  where

  processDecls :: [(Ident, (SeqNum, (Range, Range), Decl, a))] -> DeclMap -> IO DeclMap
  processDecls ((x, (s, (_, o), d, _)) : ds) m | isPublic d && not (M.member s m) =
    execStateT (checkDecl' o s d) (M.insert s (Right x) m) >>= processDecls ds
  processDecls (_ : ds) m = processDecls ds m
  processDecls [] m = return m

  checkDecl' :: Range -> SeqNum -> Decl -> StateT DeclMap IO ()
  checkDecl' _ _ (DTerm _ _) = return ()
  checkDecl' o s (DAxiom _ hs ret) = mapM_ (checkSExpr o s) hs >> checkSExpr o s ret
  checkDecl' _ _ (DDef _ _ _ Nothing) = return ()
  checkDecl' o s (DDef _ _ _ (Just (_, e))) = checkSExpr o s e
  checkDecl' o s (DTheorem _ _ hs ret pr) = do
    mapM_ (checkSExpr o s . snd) hs
    checkSExpr o s ret
    lift pr >>= mapM_ (checkProof o s)

  checkDecl :: Range -> SeqNum -> Ident -> StateT DeclMap IO ()
  checkDecl o s x = case H.lookup x (eDecls env) of
    Just (s', (_, o'), d, _) -> do
      unless (s' < s) $ lift $ reportErr o $ T.pack (show x) <> " is forward-referenced"
      m <- get
      unless (M.member s' m) $ modify (M.insert s' (Right x)) >> checkDecl' o' s' d
    Nothing -> lift $ reportErr o $ "unknown declaration " <> T.pack (show x)

  checkSExpr :: Range -> SeqNum -> SExpr -> StateT DeclMap IO ()
  checkSExpr _ _ (SVar _) = return ()
  checkSExpr o s (App t es) = checkDecl o s t >> mapM_ (checkSExpr o s) es

  checkProof :: Range -> SeqNum -> Proof -> StateT DeclMap IO ()
  checkProof _ _ (ProofHyp _) = return ()
  checkProof o s (ProofThm t es ps) =
    checkDecl o s t >> mapM_ (checkSExpr o s) es >> mapM_ (checkProof o s) ps
  checkProof o s (ProofConv _ c p) = checkConv o s c >> checkProof o s p
  checkProof o s (ProofLet _ p1 p2) = checkProof o s p1 >> checkProof o s p2

  checkConv :: Range -> SeqNum -> Conv -> StateT DeclMap IO ()
  checkConv _ _ (CVar _) = return ()
  checkConv o s (CApp t cs) = checkDecl o s t >> mapM_ (checkConv o s) cs
  checkConv o s (CSym c) = checkConv o s c
  checkConv o s (CUnfold t es _ c) =
    checkDecl o s t >> mapM_ (checkSExpr o s) es >> checkConv o s c

data IOMapping a = IOMapping (IORef (M.Map Ident Int)) (VD.IOVector (Ident, a))
data Mapping a = Mapping {mIx :: M.Map Ident Int, mArr :: V.Vector (Ident, a)}

newIOMapping :: IO (IOMapping a)
newIOMapping = liftM2 IOMapping (newIORef def) (VD.new 0)

pushIO :: IOMapping a -> Ident -> a -> IO ()
pushIO (IOMapping m v) x a = do
  n <- VD.length v
  VD.pushBack v (x, a)
  modifyIORef m $ M.insert x n

freezeMapping :: IOMapping a -> IO (Mapping a)
freezeMapping (IOMapping m v) = liftM2 Mapping (readIORef m) (VD.unsafeFreeze v)

data TermData = TermData (V.Vector PBinder) DepType (Maybe ([(VarName, Sort)], SExpr))
data ThmData = ThmData (V.Vector PBinder) [SExpr] SExpr (Maybe Proof)

data Tables = Tables {
  tSorts :: Mapping SortData,
  tTerms :: Mapping TermData,
  tThms :: Mapping ThmData }

buildTables :: Env -> [Either Sort Ident] -> IO Tables
buildTables env ds = do
  sorts <- newIOMapping
  terms <- newIOMapping
  thms <- newIOMapping
  forM_ ds $ \case
    Left s -> pushIO sorts s (thd3 (eSorts env H.! s))
    Right x -> case eDecls env H.! x of
      (_, _, DTerm bis ret, _) -> pushIO terms x (TermData (V.fromList bis) ret Nothing)
      (_, _, DDef _ bis ret val, _) -> pushIO terms x (TermData (V.fromList bis) ret val)
      (_, _, DAxiom bis hs ret, _) -> pushIO thms x (ThmData (V.fromList bis) hs ret Nothing)
      (_, _, DTheorem _ bis hs ret val, _) -> do
        pf <- fromJust <$> val
        pushIO thms x (ThmData (V.fromList bis) (snd <$> hs) ret (Just pf))
  liftM3 Tables (freezeMapping sorts) (freezeMapping terms) (freezeMapping thms)

type Fixup = (Integer, BS.ByteString)
putExportM :: Handle -> ExportM a -> IO a
putExportM h m = do
  (a, (b, Endo fixups)) <- either die pure (evalRWST m () 0)
  BL.hPut h $ BB.toLazyByteString b
  forM_ (reverse $ fixups []) $ \(pos, val) -> do
    hSeek h AbsoluteSeek pos
    BS.hPut h val
  return a

writeMM0B :: Tables -> [Either Sort Ident] -> ExportM ()
writeMM0B (Tables sorts terms thms) decls = do
  writeBS "MM0B"                     -- magic
  writeU8 (1 :: Word32)              -- version
  let numSorts = V.length (mArr sorts)
  guardError "too many sorts (max 128)" (numSorts <= 128)
  writeU8 numSorts                   -- num_sorts
  writeU16 (0 :: Word16)             -- reserved
  writeU32 $ V.length $ mArr terms   -- num_terms
  writeU32 $ V.length $ mArr thms    -- num_thms
  pTermsFixup <- fixup32
  pThmsFixup <- fixup32
  pProofFixup <- fixup32
  writeU64 (0 :: Word64) -- pIndexFixup <- fixup64
  forM_ (mArr sorts) $ writeSortData . snd
  alignTo 8 >> pTermsFixup
  forM (mArr terms) (writeTerm . snd) >>= sequence_
  alignTo 8 >> pThmsFixup
  forM (mArr thms) (writeThm . snd) >>= sequence_
  pProofFixup
  writeDecls decls
  where

  writeTerm :: TermData -> ExportM (ExportM ())
  writeTerm (TermData bis (DepType s vs) _val) = do
    writeU8 (mIx sorts M.! s .|. flag (not $ null vs) 128)
    guardError "term has more than 255 args" (V.length bis <= 255)
    writeU8 $ V.length bis
    error "unimplemented"
    -- case val of
    --   Nothing -> -1
    --   Just (ds, v) -> do
    --     let vds = V.fromList ds
    --       guardError "term has more than 255 args" (V.length bis <= 255)

  writeThm :: ThmData -> ExportM (ExportM ())
  writeThm (ThmData _bis _hs _ret _val) = error "unimplemented"

  writeDecls :: [Either Sort Ident] -> ExportM ()
  writeDecls _ = error "unimplemented"

type ExportM = RWST () (BB.Builder, Endo [Fixup]) Word64 (Either String)

flag :: Num a => Bool -> a -> a
flag False _ = 0
flag True n = n

makeFixup :: Num a => (a -> BB.Builder) -> Int -> ExportM (ExportM ())
makeFixup f n = do
  ix <- fromIntegral <$> get
  tell (f 0, mempty) >> modify (+ fromIntegral n)
  return $ get >>= \pos ->
    tell (mempty, Endo ((ix, BL.toStrict $ BB.toLazyByteString $ f $ fromIntegral pos) :))

fixup32 :: ExportM (ExportM ())
fixup32 = makeFixup BB.putWord32le 4

fixup64 :: ExportM (ExportM ())
fixup64 = makeFixup BB.putWord64le 8

writeBS :: BS.ByteString -> ExportM ()
writeBS s = tell (BB.fromByteString s, mempty) >> modify (+ fromIntegral (BS.length s))

alignTo :: Int -> ExportM ()
alignTo n = get >>= \ix -> padN $ fromIntegral (-ix `mod` fromIntegral n)

padN :: Int -> ExportM ()
padN n = writeBS (BS.replicate n 0)

writeU8 :: Integral a => a -> ExportM ()
writeU8 w = tell (BB.singleton $ fromIntegral w, mempty) >> modify (+ 1)

writeU16 :: Integral a => a -> ExportM ()
writeU16 w = tell (BB.putWord16le $ fromIntegral w, mempty) >> modify (+ 2)

writeU32 :: Integral a => a -> ExportM ()
writeU32 w = tell (BB.putWord32le $ fromIntegral w, mempty) >> modify (+ 4)

writeU64 :: Integral a => a -> ExportM ()
writeU64 w = tell (BB.putWord64le $ fromIntegral w, mempty) >> modify (+ 8)

writeSortData :: SortData -> ExportM ()
writeSortData (SortData p s pr f) =
  writeU8 (flag p 1 .|. flag s 2 .|. flag pr 4 .|. flag f 8 :: Word8)
