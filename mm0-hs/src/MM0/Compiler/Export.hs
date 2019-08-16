{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DeriveGeneric, DeriveFunctor, DeriveTraversable, TypeFamilies #-}
module MM0.Compiler.Export (export) where

import GHC.Generics (Generic)
import Control.Applicative
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.RWS.Strict
import Data.Bits
import Data.Default
import Data.Foldable
import Data.Hashable
import Data.Reify
import Data.IORef
import Data.Maybe
import Data.Word
import System.IO
import System.IO.Unsafe
import System.Exit
import qualified Data.Map.Strict as M
import qualified Data.HashMap.Strict as H
import qualified Data.IntMap as I
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.Binary.Builder as BB
import qualified Data.Vector as V
import qualified Data.Vector.Mutable.Dynamic as VD
import qualified Data.Text as T
import MM0.Compiler.Env hiding (reportErr, getTerm, getThm)
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

data ProofF a =
    SVarF VarName
  | SAppF TermName [a]

  | CVarF VarName
  | CAppF TermName [a]
  | CSymF a
  | CUnfoldF TermName [a] [VarName] a

  | PHypF VarName
  | PThmF ThmName [a] [a]
  | PConvF a a a
  | PLetF VarName a a

  | ProofF [(Maybe VarName, a)] Bool a
  deriving (Generic, Functor, Foldable, Traversable)
instance Hashable a => Hashable (ProofF a) where

instance MuRef SExpr where
  type DeRef SExpr = ProofF
  mapDeRef _ (SVar v) = pure $ SVarF v
  mapDeRef f (App t es) = SAppF t <$> traverse f es

instance MuRef Conv where
  type DeRef Conv = ProofF
  mapDeRef _ (CVar v) = pure $ CVarF v
  mapDeRef f (CApp t es) = CAppF t <$> traverse f es
  mapDeRef f (CSym c) = CSymF <$> f c
  mapDeRef f (CUnfold t es xs c) =
    liftA2 (flip (CUnfoldF t) xs) (traverse f es) (f c)

instance MuRef Proof where
  type DeRef Proof = ProofF
  mapDeRef _ (ProofHyp v) = pure $ PHypF v
  mapDeRef f (ProofThm t es ps) = liftA2 (PThmF t) (traverse f es) (traverse f ps)
  mapDeRef f (ProofConv e c p) = liftA3 PConvF (f e) (f c) (f p)
  mapDeRef f (ProofLet x p1 p2) = liftA2 (PLetF x) (f p1) (f p2)

data ProofStmt = ProofStmt [(Maybe VarName, SExpr)] SExpr (Maybe Proof)

instance MuRef ProofStmt where
  type DeRef ProofStmt = ProofF
  mapDeRef f (ProofStmt hs ret Nothing) =
    liftA2 (flip ProofF False) (traverse (traverse f) hs) (f ret)
  mapDeRef f (ProofStmt hs _ (Just p)) =
    liftA2 (flip ProofF True) (traverse (traverse f) hs) (f p)

data ProofE =
    SVarE VarName Int
  | SAppE Int [Int]

  | CReflE Int
  | CSymE Int
  | CCongE Int [Int]
  | CUnfoldE Int Int [Int] Int

  | PHypE VarName
  | PThmE Int [Int] [Int] Int
  | PConvE Int Int Int

  | ProofE [(Maybe VarName, Int)] Bool Int
  deriving (Generic, Eq)
instance Hashable ProofE where

data Name = SortName Sort | TermName TermName | ThmName ThmName
nIdent :: Name -> Ident
nIdent (SortName s) = s
nIdent (TermName s) = s
nIdent (ThmName s) = s

type DeclMap = M.Map SeqNum Name
collectDecls :: Env -> IO [Name]
collectDecls env = do
  m <- processDecls (H.toList (eDecls env)) M.empty
  return $ M.elems $ H.foldlWithKey' (\m' x (s, _, _) -> M.insert s (SortName x) m') m (eSorts env)
  where

  processDecls :: [(Ident, (SeqNum, (Range, Range), Decl, a))] -> DeclMap -> IO DeclMap
  processDecls ((x, (s, (_, o), d, _)) : ds) m | isPublic d && not (M.member s m) =
    execStateT (checkDecl' o s x d) m >>= processDecls ds
  processDecls (_ : ds) m = processDecls ds m
  processDecls [] m = return m

  checkDecl' :: Range -> SeqNum -> Ident -> Decl -> StateT DeclMap IO ()
  checkDecl' _ s x (DTerm _ _) = modify (M.insert s (TermName x))
  checkDecl' o s x (DAxiom _ hs ret) = do
    modify (M.insert s (ThmName x))
    mapM_ (checkSExpr o s) hs
    checkSExpr o s ret
  checkDecl' _ s x (DDef _ _ _ Nothing) = modify (M.insert s (TermName x))
  checkDecl' o s x (DDef _ _ _ (Just (_, e))) =
    modify (M.insert s (TermName x)) >> checkSExpr o s e
  checkDecl' o s x (DTheorem _ _ hs ret pr) = do
    modify (M.insert s (ThmName x))
    mapM_ (checkSExpr o s . snd) hs
    checkSExpr o s ret
    lift pr >>= mapM_ (checkProof o s)

  checkDecl :: Range -> SeqNum -> Ident -> StateT DeclMap IO ()
  checkDecl o s x = case H.lookup x (eDecls env) of
    Just (s', (_, o'), d, _) -> do
      unless (s' < s) $ lift $ reportErr o $ T.pack (show x) <> " is forward-referenced"
      m <- get
      unless (M.member s' m) $ checkDecl' o' s' x d
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

data TermData = TermData Visibility (V.Vector PBinder) DepType (Maybe ([(VarName, Sort)], SExpr))
data ThmData = ThmData Visibility (V.Vector PBinder) ProofStmt

data Tables = Tables {
  _tSorts :: Mapping SortData,
  _tTerms :: Mapping TermData,
  _tThms :: Mapping ThmData }

buildTables :: Env -> [Name] -> IO Tables
buildTables env ds = do
  sorts <- newIOMapping
  terms <- newIOMapping
  thms <- newIOMapping
  forM_ ds $ \case
    SortName s -> pushIO sorts s (thd3 (eSorts env H.! s))
    d -> case eDecls env H.! (nIdent d) of
      (_, _, DTerm bis ret, _) ->
        pushIO terms (nIdent d) (TermData Public (V.fromList bis) ret Nothing)
      (_, _, DDef vis bis ret val, _) ->
        pushIO terms (nIdent d) (TermData vis (V.fromList bis) ret val)
      (_, _, DAxiom bis hs ret, _) ->
        pushIO thms (nIdent d) $ ThmData Public (V.fromList bis) $
          ProofStmt ((,) Nothing <$> hs) ret Nothing
      (_, _, DTheorem vis bis hs ret val, _) -> do
        pf <- fromJust <$> val
        pushIO thms (nIdent d) $ ThmData vis (V.fromList bis) $
          ProofStmt hs ret (Just pf)
  liftM3 Tables (freezeMapping sorts) (freezeMapping terms) (freezeMapping thms)

putExportM :: Handle -> ExportM a -> IO a
putExportM h m = do
  (a, b) <- either die pure (evalRWST m () 0)
  BL.hPut h $ BB.toLazyByteString b
  return a

type UnifyM = RWST () (Endo [UnifyCmd])
  (Int, H.HashMap Ident Int, H.HashMap Ident Sort) (Either String)
type ProofM = RWST (V.Vector (ProofE, Bool), H.HashMap ProofE Int)
  (Endo [ProofCmd]) (Int, I.IntMap Int) (Either String)

writeMM0B :: Tables -> [Name] -> ExportM ()
writeMM0B (Tables sorts terms thms) decls = do
  writeBS "MM0B"                                    -- magic
  writeU8 1                                         -- version
  let numSorts = V.length (mArr sorts)
  guardError "too many sorts (max 128)" (numSorts <= 128)
  writeU8 $ fromIntegral numSorts                   -- num_sorts
  writeU16 0                                        -- reserved
  writeU32 $ fromIntegral $ V.length $ mArr terms   -- num_terms
  writeU32 $ fromIntegral $ V.length $ mArr thms    -- num_thms
  fixup32 $ fixup32 $ fixup32 $ do                  -- pTerms, pThms, pProof
    writeU64 0                                      -- pIndex
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
      writeU64 (shiftL 1 63 .|. shiftL (fromIntegral $ mIx sorts M.! s) 56 .|. shiftL 1 ln)
      m (ln+1) (H.insert x ln lctx) (n+1) (H.insert x n ctx)
    go (PReg v (DepType s xs)) m ln lctx n ctx = do
      writeU64 $ foldl' (\w x -> w .|. shiftL 1 (lctx H.! x))
        (shiftL (fromIntegral $ mIx sorts M.! s) 56) xs
      m ln lctx (n+1) (H.insert v n ctx)

  runUnify :: (Int, H.HashMap Ident Int, H.HashMap Ident Sort) -> UnifyM () -> Either String [UnifyCmd]
  runUnify s m = evalRWST m () s <&> \(_, Endo f) -> f []

  sExprUnify :: SExpr -> UnifyM ()
  sExprUnify (SVar v) = do
    (n, vm, dm) <- get
    case H.lookup v dm of
      Nothing -> tell (Endo (URef (fromIntegral (vm H.! v)) :))
      Just s -> do
        tell (Endo (UDummy (fromIntegral (mIx sorts M.! s)) :))
        put (n+1, H.insert v n vm, H.delete v dm)
  sExprUnify (App t es) = do
    t' <- getTerm t
    tell (Endo (UTerm (fromIntegral t') :))
    mapM_ sExprUnify es

  writeTermHead :: (TermData, Word32) -> ExportM ()
  writeTermHead (TermData _ bis (DepType s _) val, pTerm) = do
    guardError "term has more than 65536 args" (V.length bis < 65536)
    writeU16 $ fromIntegral $ V.length bis
    writeU8 $ fromIntegral $ mIx sorts M.! s .|. flag (not $ null val) 128
    writeU8 0
    writeU32 pTerm

  writeTerm :: (Ident, TermData) -> ExportM (TermData, Word32)
  writeTerm (t, td@(TermData _ bis (DepType sret vs) val)) = do
    pTerm <- fromIntegral <$> get
    writeBis bis $ \_ lctx n ctx -> do
      writeU64 $ foldl' (\w x -> w .|. shiftL 1 (lctx H.! x))
        (shiftL (fromIntegral (mIx sorts M.! sret)) 56) vs
      case val of
        Nothing -> return ()
        Just (ds, e) -> do
          us <- liftEither $ withContext t $
            runUnify (n, ctx, H.fromList ds) (sExprUnify e)
          writeUnify us
    return (td, pTerm)

  writeThmHead :: (ThmData, Word32) -> ExportM ()
  writeThmHead (ThmData _ bis _, pThm) = do
    guardError "theorem has more than 65536 args" (V.length bis < 65536)
    writeU16 $ fromIntegral $ V.length bis
    writeU16 0
    writeU32 pThm

  writeThm :: (Ident, ThmData) -> ExportM (ThmData, Word32)
  writeThm (x, td@(ThmData _ bis (ProofStmt hs ret _))) = do
    pThm <- fromIntegral <$> get
    writeBis bis $ \_ _ n ctx -> do
      us <- liftEither $ withContext x $ runUnify (n, ctx, H.empty) $ do
        forM_ hs $ \(_, h) -> tell (Endo (UHyp :)) >> sExprUnify h
        tell (Endo (UThm :)) >> sExprUnify ret
      writeUnify us
    return (td, pThm)

  getTerm :: MonadError String m => TermName -> m Int
  getTerm t = fromJustError ("unknown term " ++ T.unpack t) (M.lookup t (mIx terms))

  getThm :: MonadError String m => ThmName -> m Int
  getThm t = fromJustError ("unknown theorem " ++ T.unpack t) (M.lookup t (mIx thms))

  writeDecl :: Name -> ExportM ()
  writeDecl (SortName _) = do
    writeU8 0x04   -- CMD_STMT_SORT
    writeU32 5 -- sizeof(cmd_stmt)
  writeDecl (TermName t) = case snd $ mArr terms V.! (mIx terms M.! t) of
    TermData _ _ _ Nothing -> do
      writeU8 0x05   -- CMD_STMT_TERM
      writeU32 5 -- sizeof(cmd_stmt)
    TermData vis bis (DepType s _) (Just (_, e)) -> do
      start <- get
      writeU8 (flag (vis == Local) 0x08 .|. 0x05) -- CMD_STMT_DEF,  CMD_STMT_LOCAL_DEF
      fixup32 $ do
        lift (withContext t $ runProof bis (Just s) e) >>= mapM_ writeProofCmd
        end <- get
        return ((), fromIntegral (end - start))
  writeDecl (ThmName t) = do
    let ThmData vis bis p@(ProofStmt _ _ val) = snd $ mArr thms V.! (mIx thms M.! t)
    start <- get
    writeU8 $ if isJust val
      then flag (vis == Local) 0x08 .|. 0x05 -- CMD_STMT_THM, CMD_STMT_LOCAL_THM
      else 0x02 -- CMD_STMT_AXIOM
    fixup32 $ do
      lift (withContext t $ runProof bis Nothing p) >>= mapM_ writeProofCmd
      end <- get
      return ((), fromIntegral (end - start))

  toProofE :: I.IntMap (ProofF Int) -> VD.IOVector (ProofE, Bool) ->
    IORef (H.HashMap ProofE Int) -> H.HashMap VarName Sort ->
    (Maybe Sort -> Int -> ExceptT String IO ProofE,
      ProofE -> ExceptT String IO Int)
  toProofE im vec m args = (toE, hashCons) where
    hashCons :: ProofE -> ExceptT String IO Int
    hashCons p = H.lookup p <$> lift (readIORef m) >>= \case
      Nothing -> do
        n <- VD.length vec
        VD.pushBack vec (p, False)
        lift $ modifyIORef m (H.insert p n)
        return n
      Just n -> do
        (p', b) <- VD.read vec n
        unless b $ VD.write vec n (p', True)
        return n

    substE :: H.HashMap VarName Int -> SExpr -> ExceptT String IO Int
    substE subst (SVar v) = return (subst H.! v)
    substE subst (App t es) = do
      t' <- getTerm t
      es' <- mapM (substE subst) es
      hashCons (SAppE t' es')

    toIx :: Maybe Sort -> Int -> ExceptT String IO Int
    toIx tgt i = toE tgt i >>= hashCons

    toE :: Maybe Sort -> Int -> ExceptT String IO ProofE
    toE tgt ix = case im I.! ix of
      SVarF v -> case tgt <|> H.lookup v args of
        Just s -> return $ SVarE v (mIx sorts M.! s)
        Nothing -> throwError $ "unknown dummy sort for " ++ T.unpack v
      SAppF t es -> do
        t' <- getTerm t
        let (_, TermData _ bis _ _) = mArr terms V.! t'
        SAppE t' <$> zipWithM (toIx . Just . dSort . binderType) (toList bis) es
      CVarF v -> case tgt <|> H.lookup v args of
        Just s -> CReflE <$> hashCons (SVarE v (mIx sorts M.! s))
        Nothing -> throwError $ "unknown dummy sort for " ++ T.unpack v
      CSymF c -> toE tgt c >>= \case
        CReflE i -> return (CReflE i)
        p -> CSymE <$> hashCons p
      CAppF t cs -> do
        t' <- getTerm t
        let (_, TermData _ bis _ _) = mArr terms V.! t'
        cs' <- zipWithM (toE . Just . dSort . binderType) (toList bis) cs
        case sequence (cs' <&> \case CReflE i -> Just i; _ -> Nothing) of
          Nothing -> CCongE t' <$> mapM hashCons cs'
          Just ns -> CReflE <$> hashCons (SAppE t' ns)
      CUnfoldF t es xs c -> do
        t' <- getTerm t
        let (_, TermData _ bis _ val) = mArr terms V.! t'
        (ds, v) <- fromJustError (T.unpack t ++ " is not a definition") val
        es' <- zipWithM (toIx . Just . dSort . binderType) (toList bis) es
        e1 <- hashCons (SAppE t' es')
        xs' <- zipWithM (\(_, s) x -> hashCons (SVarE x (mIx sorts M.! s))) ds xs
        e2 <- substE (H.fromList
          (zip (binderName <$> toList bis) es' ++ zip (fst <$> ds) xs')) v
        CUnfoldE e1 e2 xs' <$> toIx tgt c
      PHypF h -> return (PHypE h)
      PThmF t es ps -> do
        t' <- getThm t
        let (_, ThmData _ bis (ProofStmt _ ret _)) = mArr thms V.! t'
        es' <- zipWithM (toIx . Just . dSort . binderType) (toList bis) es
        ps' <- mapM (toIx Nothing) ps
        ret' <- substE (H.fromList (zip (binderName <$> toList bis) es')) ret
        return (PThmE t' es' ps' ret')
      PConvF e c p -> do
        e' <- toIx Nothing e
        toE Nothing c >>= \case
          CReflE _ -> toE Nothing p
          c' -> liftA2 (PConvE e') (hashCons c') (toIx Nothing p)
      PLetF x p1 p2 -> do
        n <- toIx Nothing p1
        lift $ modifyIORef m (H.insert (PHypE x) n)
        toE tgt p2
      ProofF hs th ret -> do
        hs' <- forM hs $ \(v, n) -> (,) v <$> toIx Nothing n
        ProofE hs' th <$> toIx Nothing ret

  runProof :: (MuRef a, DeRef a ~ ProofF) =>
    V.Vector PBinder -> Maybe Sort -> a -> Either String [ProofCmd]
  runProof bis s a = do
    (st, bis2, pe2) <- unsafePerformIO $ runExceptT $ do
      Graph pairs root <- lift $ reifyGraph a
      let m = I.fromList pairs
      v <- lift $ VD.new 0
      h <- lift $ newIORef H.empty
      let (toE, hashCons) = toProofE m v h (H.fromList
            ((\bi -> (binderName bi, dSort $ binderType bi)) <$> toList bis))
      bis' <- forM bis $ \bi -> do
        let x = binderName bi
        hashCons $ SVarE x $ mIx sorts M.! dSort (binderType bi)
      pe <- toE s root >>= hashCons
      v' <- VD.unsafeFreeze v
      h' <- lift (readIORef h)
      return ((v', h'), bis', pe)
    (_, Endo f) <- evalRWST (mapM pushHeap bis2 >> mkProof pe2) st (0, I.empty)
    return (f [])

  pushHeap :: Int -> ProofM ()
  pushHeap n = modify $ \(k, heap) -> (k+1, I.insert n k heap)

  mkProof :: Int -> ProofM ()
  mkProof n = I.lookup n . snd <$> get >>= \case
    Just i -> tell $ Endo (PRef (fromIntegral i) :)
    Nothing -> (V.! n) . fst <$> ask >>= \case
      (SVarE _ s, _) -> tell (Endo (PDummy (fromIntegral s) :)) >> pushHeap n
      (SAppE t es, save) -> mapM_ mkProof es >>
        if save then do
          tell $ Endo (PTermSave (fromIntegral t) :)
          pushHeap n
        else tell $ Endo (PTerm (fromIntegral t) :)
      (CReflE _, _) -> tell $ Endo (PRefl :)
      (CSymE e, _) -> tell (Endo (PSym :)) >> mkProof e
      (CCongE _ cs, _) -> tell (Endo (PCong :)) >> mapM_ mkProof cs
      (CUnfoldE e1 e2 _ c, _) -> mkProof e1 >> mkProof e2 >>
        tell (Endo (PUnfold :)) >> mkProof c
      (PHypE h, _) -> throwError $ "unknown hypothesis " ++ T.unpack h
      (PThmE t es ps e, save) ->
        mapM mkProof ps >> mapM mkProof es >> mkProof e >>
        if save then do
          tell $ Endo (PThmSave (fromIntegral t) :)
          pushHeap n
        else tell $ Endo (PThm (fromIntegral t) :)
      (PConvE e c p, _) ->
        mkProof e >> mkProof p >> tell (Endo (PConv :)) >> mkProof c
      (ProofE hs _ ret, _) -> do
        forM_ hs $ \(h, i) -> do
          mkProof i >> tell (Endo (PHyp :))
          (_, heap) <- ask
          case h >>= flip H.lookup heap . PHypE of
            Nothing -> modify $ mapFst (+1)
            Just k -> pushHeap k
        mkProof ret

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

_fixup64 :: ExportM (r, Word64) -> ExportM r
_fixup64 = makeFixup BB.putWord64le 8

writeBS :: BS.ByteString -> ExportM ()
writeBS s = tell (BB.fromByteString s) >> modify (+ fromIntegral (BS.length s))

alignTo :: Int -> ExportM ()
alignTo n = get >>= \ix -> padN $ fromIntegral (-ix `mod` fromIntegral n)

padN :: Int -> ExportM ()
padN n = writeBS (BS.replicate n 0)

writeU8 :: Word8 -> ExportM ()
writeU8 w = tell (BB.singleton w) >> modify (+ 1)

writeU16 :: Word16 -> ExportM ()
writeU16 w = tell (BB.putWord16le w) >> modify (+ 2)

writeU32 :: Word32 -> ExportM ()
writeU32 w = tell (BB.putWord32le w) >> modify (+ 4)

writeU64 :: Word64 -> ExportM ()
writeU64 w = tell (BB.putWord64le w) >> modify (+ 8)

writeSortData :: SortData -> ExportM ()
writeSortData (SortData p s pr f) =
  writeU8 (flag p 1 .|. flag s 2 .|. flag pr 4 .|. flag f 8)

data UnifyCmd =
    UTerm Word32
  | UTermSave Word32
  | URef Word32
  | UDummy Word32
  | UThm
  | UHyp

writeCmd :: Word8 -> Word32 -> ExportM ()
writeCmd c 0 = writeU8 c
writeCmd c n | n < 0x100 = writeU8 (c .|. 0x40) >> writeU8 (fromIntegral n)
writeCmd c n | n < 0x10000 = writeU8 (c .|. 0x80) >> writeU16 (fromIntegral n)
writeCmd c n = writeU8 (c .|. 0xC0) >> writeU32 n

writeUnifyCmd :: UnifyCmd -> ExportM ()
writeUnifyCmd (UTerm n)     = writeCmd 0x30 n
writeUnifyCmd (UTermSave n) = writeCmd 0x31 n
writeUnifyCmd (URef n)      = writeCmd 0x32 n
writeUnifyCmd (UDummy n)    = writeCmd 0x33 n
writeUnifyCmd UThm          = writeU8 0x34
writeUnifyCmd UHyp          = writeU8 0x36

writeUnify :: [UnifyCmd] -> ExportM ()
writeUnify l = mapM writeUnifyCmd l >> writeU8 0

data ProofCmd =
    PTerm Word32
  | PTermSave Word32
  | PRef Word32
  | PDummy Word32
  | PThm Word32
  | PThmSave Word32
  | PHyp
  | PConv
  | PRefl
  | PSym
  | PCong
  | PUnfold
  | PConvCut
  | PConvRef Word32

writeProofCmd :: ProofCmd -> ExportM ()
writeProofCmd (PTerm n)     = writeCmd 0x10 n
writeProofCmd (PTermSave n) = writeCmd 0x11 n
writeProofCmd (PRef n)      = writeCmd 0x12 n
writeProofCmd (PDummy n)    = writeCmd 0x13 n
writeProofCmd (PThm n)      = writeCmd 0x14 n
writeProofCmd (PThmSave n)  = writeCmd 0x15 n
writeProofCmd PHyp          = writeU8 0x16
writeProofCmd PConv         = writeU8 0x17
writeProofCmd PRefl         = writeU8 0x18
writeProofCmd PSym          = writeU8 0x19
writeProofCmd PCong         = writeU8 0x1A
writeProofCmd PUnfold       = writeU8 0x1B
writeProofCmd PConvCut      = writeU8 0x1C
writeProofCmd (PConvRef n)  = writeCmd 0x1D n
