module MM0.Compiler.Export where

import Control.Monad.State
import Control.Monad.RWS.Strict
import Data.Bits
import Data.Default
import Data.Foldable
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

type DeclMap = M.Map SeqNum (Either Sort (Ident, Decl))
collectDecls :: Env -> IO [Either Sort (Ident, Decl)]
collectDecls env = do
  m <- processDecls (H.toList (eDecls env)) M.empty
  return $ M.elems $ H.foldlWithKey' (\m' x (s, _, _) -> M.insert s (Left x) m') m (eSorts env)
  where

  processDecls :: [(Ident, (SeqNum, (Range, Range), Decl, a))] -> DeclMap -> IO DeclMap
  processDecls ((x, (s, (_, o), d, _)) : ds) m | isPublic d && not (M.member s m) =
    execStateT (checkDecl' o s d) (M.insert s (Right (x, d)) m) >>= processDecls ds
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
      unless (M.member s' m) $ modify (M.insert s' (Right (x, d))) >> checkDecl' o' s' d
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

buildTables :: Env -> [Either Sort (Ident, Decl)] -> IO Tables
buildTables env ds = do
  sorts <- newIOMapping
  terms <- newIOMapping
  thms <- newIOMapping
  forM_ ds $ \case
    Left s -> pushIO sorts s (thd3 (eSorts env H.! s))
    Right (x, _) -> case eDecls env H.! x of
      (_, _, DTerm bis ret, _) -> pushIO terms x (TermData (V.fromList bis) ret Nothing)
      (_, _, DDef _ bis ret val, _) -> pushIO terms x (TermData (V.fromList bis) ret val)
      (_, _, DAxiom bis hs ret, _) -> pushIO thms x (ThmData (V.fromList bis) hs ret Nothing)
      (_, _, DTheorem _ bis hs ret val, _) -> do
        pf <- fromJust <$> val
        pushIO thms x (ThmData (V.fromList bis) (snd <$> hs) ret (Just pf))
  liftM3 Tables (freezeMapping sorts) (freezeMapping terms) (freezeMapping thms)

putExportM :: Handle -> ExportM a -> IO a
putExportM h m = do
  (a, b) <- either die pure (evalRWST m () 0)
  BL.hPut h $ BB.toLazyByteString b
  return a

writeMM0B :: Tables -> [Either Sort (Ident, Decl)] -> ExportM ()
writeMM0B (Tables sorts terms thms) decls = do
  writeBS "MM0B"                     -- magic
  writeU8 (1 :: Word32)              -- version
  let numSorts = V.length (mArr sorts)
  guardError "too many sorts (max 128)" (numSorts <= 128)
  writeU8 numSorts                   -- num_sorts
  writeU16 (0 :: Word16)             -- reserved
  writeU32 $ V.length $ mArr terms   -- num_terms
  writeU32 $ V.length $ mArr thms    -- num_thms
  fixup32 $ fixup32 $ fixup32 $ do   -- pTerms, pThms, pProof
    writeU64 (0 :: Word64)           -- pIndex
    forM_ (mArr sorts) $ writeSortData . snd
    pTerms <- alignTo 8 >> fromIntegral <$> get
    revision (mapM_ writeTermHead)
      (8 * fromIntegral (V.length (mArr terms)))
      ((,) () <$> forM (mArr terms) writeTerm)
    pThms <- alignTo 8 >> fromIntegral <$> get
    revision (mapM_ writeThmHead)
      (8 * fromIntegral (V.length (mArr thms)))
      ((,) () <$> forM (mArr thms) writeThm)
    pProof <- fromIntegral <$> get
    return ((((), pTerms), pThms), pProof)
  mapM_ writeDecl decls
  where

  writeBis :: V.Vector PBinder ->
    (Int -> H.HashMap VarName Int -> Int -> H.HashMap VarName Int -> ExportM ()) ->
    ExportM ()
  writeBis bis f = foldr go f bis 0 H.empty 0 H.empty where
    go (PBound x s) m ln lctx n ctx = do
      guardError "term has more than 56 bound variables" (ln < 56)
      writeU64 (shiftL 1 63 .|. shiftL (mIx sorts M.! s) 56 .|. shiftL 1 ln)
      m (ln+1) (H.insert x ln lctx) (n+1) (H.insert x n ctx)
    go (PReg v (DepType s xs)) m ln lctx n ctx = do
      writeU64 $ foldl' (\w x -> w .|. shiftL 1 (lctx H.! x))
        (shiftL (mIx sorts M.! s) 56) xs
      m ln lctx (n+1) (H.insert v n ctx)

  runUnify :: RWS () (Endo [UnifyCmd]) (Int, H.HashMap Ident Int, H.HashMap Ident Sort) () -> (Int, H.HashMap Ident Int, H.HashMap Ident Sort) -> [UnifyCmd]
  runUnify m s = case evalRWS m () s of (_, Endo f) -> f []

  sExprUnify :: SExpr -> RWS () (Endo [UnifyCmd]) (Int, H.HashMap Ident Int, H.HashMap Ident Sort) ()
  sExprUnify (SVar v) = do
    (n, vm, dm) <- get
    case H.lookup v dm of
      Nothing -> tell (Endo (URef (fromIntegral (vm H.! v)) :))
      Just s -> do
        tell (Endo (UDummy (fromIntegral (mIx sorts M.! s)) :))
        put (n+1, H.insert v n vm, H.delete v dm)
  sExprUnify (App t es) =
    tell (Endo (UTerm (fromIntegral (mIx terms M.! t)) :)) >> mapM_ sExprUnify es

  writeTermHead :: (TermData, Word32) -> ExportM ()
  writeTermHead (TermData bis (DepType s _) val, pTerm) = do
    guardError "term has more than 65536 args" (V.length bis < 65536)
    writeU16 $ V.length bis
    writeU8 (mIx sorts M.! s .|. flag (not $ null val) 128)
    writeU8 (0 :: Word8)
    writeU32 pTerm

  writeTerm :: (Ident, TermData) -> ExportM (TermData, Word32)
  writeTerm (_, td@(TermData bis (DepType sret vs) val)) = do
    pTerm <- fromIntegral <$> get
    writeBis bis $ \_ lctx n ctx -> do
      writeU64 $ foldl' (\w x -> w .|. shiftL 1 (lctx H.! x))
        (shiftL (mIx sorts M.! sret) 56) vs
      case val of
        Nothing -> return ()
        Just (ds, e) -> writeUnify $ runUnify (sExprUnify e) (n, ctx, H.fromList ds)
    return (td, pTerm)

  writeThmHead :: (ThmData, Word32) -> ExportM ()
  writeThmHead (ThmData bis _ _ _, pThm) = do
    guardError "theorem has more than 65536 args" (V.length bis < 65536)
    writeU16 $ V.length bis
    writeU16 (0 :: Word16)
    writeU32 pThm

  writeThm :: (Ident, ThmData) -> ExportM (ThmData, Word32)
  writeThm (_, td@(ThmData bis hs ret _)) = do
    pThm <- fromIntegral <$> get
    writeBis bis $ \_ _ n ctx ->
      writeUnify $ flip runUnify (n, ctx, H.empty) $ do
        forM_ hs $ \h -> tell (Endo (UHyp :)) >> sExprUnify h
        tell (Endo (UThm :)) >> sExprUnify ret
    return (td, pThm)

  writeDecl :: Either Sort (Ident, Decl) -> ExportM ()
  writeDecl (Left _) = do
    writeU8 (4 :: Word8)   -- CMD_STMT_SORT
    writeU32 (5 :: Word32) -- sizeof(cmd_stmt)
  writeDecl (Right (_x, DTerm _bis _ret)) = error "unimplemented"
  writeDecl (Right (_x, DDef _ _bis _ret _val)) = error "unimplemented"
  writeDecl (Right (_x, DAxiom _bis _hs _ret)) = error "unimplemented"
  writeDecl (Right (_x, DTheorem _ _bis _hs _ret _val)) = error "unimplemented"

type ExportM = RWST () BB.Builder Word64 (Either String)

flag :: Num a => Bool -> a -> a
flag False _ = 0
flag True n = n

revision :: (a -> ExportM ()) -> Word64 -> ExportM (r, a) -> ExportM r
revision f n m = RWST $ \() ix -> do
  ((r, a), ix', w') <- runRWST m () (ix + n)
  ((), _, w) <- runRWST (f a) () ix
  return (r, ix', w <> w')

makeFixup :: (a -> BB.Builder) -> Word64 -> ExportM (r, a) -> ExportM r
makeFixup f = revision (tell . f)

fixup32 :: ExportM (r, Word32) -> ExportM r
fixup32 = makeFixup BB.putWord32le 4

fixup64 :: ExportM (r, Word64) -> ExportM r
fixup64 = makeFixup BB.putWord64le 8

writeBS :: BS.ByteString -> ExportM ()
writeBS s = tell (BB.fromByteString s) >> modify (+ fromIntegral (BS.length s))

alignTo :: Int -> ExportM ()
alignTo n = get >>= \ix -> padN $ fromIntegral (-ix `mod` fromIntegral n)

padN :: Int -> ExportM ()
padN n = writeBS (BS.replicate n 0)

writeU8 :: Integral a => a -> ExportM ()
writeU8 w = tell (BB.singleton $ fromIntegral w) >> modify (+ 1)

writeU16 :: Integral a => a -> ExportM ()
writeU16 w = tell (BB.putWord16le $ fromIntegral w) >> modify (+ 2)

writeU32 :: Integral a => a -> ExportM ()
writeU32 w = tell (BB.putWord32le $ fromIntegral w) >> modify (+ 4)

writeU64 :: Integral a => a -> ExportM ()
writeU64 w = tell (BB.putWord64le $ fromIntegral w) >> modify (+ 8)

writeSortData :: SortData -> ExportM ()
writeSortData (SortData p s pr f) =
  writeU8 (flag p 1 .|. flag s 2 .|. flag pr 4 .|. flag f 8 :: Word8)

data UnifyCmd =
    UTerm Word32
  | UTermSave Word32
  | URef Word32
  | UDummy Word32
  | UThm
  | UHyp

writeCmd :: Word8 -> Word32 -> ExportM ()
writeCmd c 0 = writeU8 c
writeCmd c n | n < 0x100 = writeU8 (c .|. 0x40) >> writeU8 n
writeCmd c n | n < 0x10000 = writeU8 (c .|. 0x80) >> writeU16 n
writeCmd c n = writeU8 (c .|. 0xC0) >> writeU32 n

writeUnifyCmd :: UnifyCmd -> ExportM ()
writeUnifyCmd (UTerm n) = writeCmd 0x30 n
writeUnifyCmd (UTermSave n) = writeCmd 0x31 n
writeUnifyCmd (URef n) = writeCmd 0x32 n
writeUnifyCmd (UDummy n) = writeCmd 0x33 n
writeUnifyCmd UThm = writeU8 (0x34 :: Word8)
writeUnifyCmd UHyp = writeU8 (0x36 :: Word8)

writeUnify :: [UnifyCmd] -> ExportM ()
writeUnify l = mapM writeUnifyCmd l >> writeU8 (0 :: Word8)
