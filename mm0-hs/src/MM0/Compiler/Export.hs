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
import qualified Data.List.NonEmpty as NE
import qualified Data.IntMap as I
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.Binary.Builder as BB
import qualified Data.Vector as V
import qualified Data.Vector.Mutable.Dynamic as VD
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import MM0.Compiler.Env hiding (reportErr, getTerm, getThm)
import qualified MM0.Kernel.Environment as K
import qualified MM0.Kernel.Types as K
import MM0.Util

export :: Bool -> String -> Env -> IO ()
export strip fname env = do
  m <- collectDecls env
  t <- liftIO $ buildTables env m
  exportTables strip fname t m

_exportK :: Bool -> String -> K.Environment -> [K.Stmt] -> IO ()
_exportK strip fname env pfs = do
  m <- collectDeclsK env
  t <- liftIO $ buildTablesK env pfs
  exportTables strip fname t m

collectDeclsK :: K.Environment -> IO [Name]
collectDeclsK = undefined

exportTables :: Bool -> String -> Tables -> [Name] -> IO ()
exportTables strip fname t m = do
  withBinaryFile fname WriteMode $ \h -> do
    hSetBuffering h (BlockBuffering Nothing)
    putExportM h (writeMM0B strip t m)

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

instance MuRef K.Conv where
  type DeRef K.Conv = ProofF
  mapDeRef _ (CVar v) = pure $ CVarF v
  mapDeRef f (CApp t es) = CAppF t <$> traverse f es
  mapDeRef f (CSym c) = CSymF <$> f c
  mapDeRef f (CUnfold t es xs c) =
    liftA2 (flip (CUnfoldF t) xs) (traverse f es) (f c)

instance MuRef K.Proof where
  type DeRef K.Proof = ProofF
  mapDeRef _ (PHyp v) = pure $ PHypF v
  mapDeRef f (PThm t es ps) = liftA2 (PThmF t) (traverse f es) (traverse f ps)
  mapDeRef f (PConv e c p) = liftA3 PConvF (f e) (f c) (f p)
  mapDeRef f (PLet x p1 p2) = liftA2 (PLetF x) (f p1) (f p2)
  mapDeRef _ PSorry = error "sorry found in proof"

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
  deriving (Generic, Eq, Show)
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
  checkProof _ _ PSorry = error "sorry found in proof"
  checkProof _ _ (PHyp _) = return ()
  checkProof o s (PThm t es ps) =
    checkDecl o s t >> mapM_ (checkSExpr o s) es >> mapM_ (checkProof o s) ps
  checkProof o s (PConv _ c p) = checkConv o s c >> checkProof o s p
  checkProof o s (PLet _ p1 p2) = checkProof o s p1 >> checkProof o s p2

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

buildTablesWith :: (IOMapping SortData ->
                    IOMapping TermData ->
                    IOMapping ThmData -> IO ()) -> IO Tables
buildTablesWith f = do
  sorts <- newIOMapping
  terms <- newIOMapping
  thms <- newIOMapping
  f sorts terms thms
  liftM3 Tables (freezeMapping sorts) (freezeMapping terms) (freezeMapping thms)

buildTables :: Env -> [Name] -> IO Tables
buildTables env ds = buildTablesWith $ \sorts terms thms ->
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

buildTablesK :: K.Environment -> [K.Stmt] -> IO Tables
buildTablesK env pfs = buildTablesWith $ \sorts terms thms ->
  forM_ pfs $ \case
    K.StepSort s -> pushIO sorts s (K.eSorts env M.! s)
    K.StepTerm t -> case K.eDecls env M.! t of
      K.DTerm bis ret -> pushIO terms t (TermData Public (V.fromList bis) ret Nothing)
      _ -> error $ "not a term: " ++ T.unpack t
    K.StepAxiom t -> case K.eDecls env M.! t of
      K.DAxiom bis hs ret ->
        pushIO thms t $ ThmData Public (V.fromList bis) $
          ProofStmt ((,) Nothing <$> hs) ret Nothing
      _ -> error $ "not an axiom: " ++ T.unpack t
    _ -> error "unimplemented"

putExportM :: Handle -> ExportM a -> IO a
putExportM h m = do
  (a, b) <- either die pure (evalRWST m () 0)
  BL.hPut h $ BB.toLazyByteString b
  return a

type UnifyM = RWST () (Endo [UnifyCmd])
  (Int, H.HashMap Ident Int, H.HashMap Ident Sort) (Either String)
type ProofM = RWST (V.Vector (ProofE, Bool), H.HashMap ProofE Int)
  (Endo [ProofCmd]) (Int, I.IntMap Int) (Either String)
type PMapping = (I.IntMap Word64, I.IntMap Word64, I.IntMap Word64)
type IndexM = StateT PMapping ExportM

writeMM0B :: Bool -> Tables -> [Name] -> ExportM ()
writeMM0B strip (Tables sorts terms thms) decls = do
  writeBS "MM0B"                                    -- magic
  writeU8 1                                         -- version
  let numSorts = V.length (mArr sorts)
  guardError "too many sorts (max 128)" (numSorts <= 128)
  writeU8 $ fromIntegral numSorts                   -- num_sorts
  writeU16 0                                        -- reserved
  writeU32 $ fromIntegral $ V.length $ mArr terms   -- num_terms
  writeU32 $ fromIntegral $ V.length $ mArr thms    -- num_thms
  fixup32 $ fixup32 $ fixup64 $ fixup64 $ do        -- pTerms, pThms, pProof, pIndex
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
    mapM_ writeDecl decls >> writeU8 0
    pIndex <- if strip then 0 <$ padN 4 else alignTo 8 >> fromIntegral <$> get
    return (((((), pTerms), pThms), pProof), pIndex)
  unless strip writeIndex
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
      ns <- forM xs $ fromJustError "bound variable not in context" . flip H.lookup lctx
      writeU64 $ foldl' (\w i -> w .|. shiftL 1 i)
        (shiftL (fromIntegral $ mIx sorts M.! s) 56) ns
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
    pTerm <- alignTo 8 >> fromIntegral <$> get
    withContext t $ writeBis bis $ \_ lctx n ctx -> do
      writeU64 $ foldl' (\w x -> w .|. shiftL 1 (lctx H.! x))
        (shiftL (fromIntegral (mIx sorts M.! sret)) 56) vs
      case val of
        Nothing -> return ()
        Just (ds, e) -> do
          us <- liftEither $ runUnify (n, ctx, H.fromList ds) (sExprUnify e)
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
    pThm <- alignTo 8 >> fromIntegral <$> get
    withContext x $ writeBis bis $ \_ _ n ctx -> do
      us <- liftEither $ runUnify (n, ctx, H.empty) $ do
        sExprUnify ret
        forM_ (reverse hs) $ \(_, h) -> tell (Endo (UHyp :)) >> sExprUnify h
      writeUnify us
    return (td, pThm)

  getTerm :: MonadError String m => TermName -> m Int
  getTerm t = fromJustError ("unknown term " ++ T.unpack t) (M.lookup t (mIx terms))

  getThm :: MonadError String m => ThmName -> m Int
  getThm t = fromJustError ("unknown theorem " ++ T.unpack t) (M.lookup t (mIx thms))

  writeDecl :: Name -> ExportM ()
  writeDecl (SortName _) = do
    writeU8 0x44   -- CMD_DATA_8 | CMD_STMT_SORT
    writeU8 2 -- sizeof(cmd8)
  writeDecl (TermName t) = case snd $ mArr terms V.! (mIx terms M.! t) of
    TermData _ _ _ Nothing -> do
      writeU8 0x45   -- CMD_DATA_8 | CMD_STMT_TERM
      writeU8 2 -- sizeof(cmd8)
    TermData vis bis (DepType s _) (Just (_, e)) -> do
      start <- get
      writeU8 (flag (vis == Local) 0x08 .|. 0xC5) -- CMD_DATA_32 | CMD_STMT_DEF, CMD_STMT_LOCAL_DEF
      fixup32 $ do
        lift (withContext t $ runProof bis (Just s) e) >>= writeProof
        end <- get
        return ((), fromIntegral (end - start))
  writeDecl (ThmName t) = do
    let ThmData vis bis p@(ProofStmt _ _ val) = snd $ mArr thms V.! (mIx thms M.! t)
    start <- get
    writeU8 $ if isJust val
      then flag (vis == Local) 0x08 .|. 0xC6 -- CMD_DATA_32 | CMD_STMT_THM, CMD_STMT_LOCAL_THM
      else 0xC2 -- CMD_DATA_32 | CMD_STMT_AXIOM
    fixup32 $ do
      lift (withContext t $ runProof bis Nothing p) >>= writeProof
      end <- get
      return ((), fromIntegral (end - start))

  toProofE :: I.IntMap (ProofF Int) -> VD.IOVector (ProofE, Bool) ->
    IORef (H.HashMap ProofE Int) -> H.HashMap VarName Sort ->
    (Maybe Sort -> Int -> ExceptT String IO ProofE,
      ProofE -> ExceptT String IO Int)
  toProofE im vec m args = (toE, hashCons) where
    incRef :: Int -> ExceptT String IO Int
    incRef n = do
      (p, b) <- VD.read vec n
      unless b $ VD.write vec n (p, True)
      return n

    hashCons :: ProofE -> ExceptT String IO Int
    hashCons p = H.lookup p <$> lift (readIORef m) >>= \case
      Nothing -> do
        n <- VD.length vec
        VD.pushBack vec (p, False)
        lift $ modifyIORef m (H.insert p n)
        return n
      Just n -> incRef n

    substE :: H.HashMap VarName Int -> SExpr -> ExceptT String IO Int
    substE subst (SVar v) = incRef (subst H.! v)
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
    Just i -> tell $ Endo (PCRef (fromIntegral i) :)
    Nothing -> (V.! n) . fst <$> ask >>= \case
      (SVarE v s, _) -> tell (Endo (PCDummy (fromIntegral s) v :)) >> pushHeap n
      (SAppE t es, save) -> mapM_ mkProof es >>
        if save then do
          tell $ Endo (PCTermSave (fromIntegral t) :)
          pushHeap n
        else tell $ Endo (PCTerm (fromIntegral t) :)
      (CReflE _, _) -> tell $ Endo (PCRefl :)
      (CSymE e, _) -> tell (Endo (PCSym :)) >> mkProof e
      (CCongE _ cs, _) -> tell (Endo (PCCong :)) >> mapM_ mkProof cs
      (CUnfoldE e1 e2 _ c, _) -> mkProof e1 >> mkProof e2 >>
        tell (Endo (PCUnfold :)) >> mkProof c
      (PHypE h, _) -> throwError $ "unknown hypothesis " ++ T.unpack h
      (PThmE t es ps e, save) ->
        mapM mkProof ps >> mapM mkProof es >> mkProof e >>
        if save then do
          tell $ Endo (PCThmSave (fromIntegral t) :)
          pushHeap n
        else tell $ Endo (PCThm (fromIntegral t) :)
      (PConvE e c p, _) ->
        mkProof e >> mkProof p >> tell (Endo (PCConv :)) >> mkProof c
      (ProofE hs _ ret, _) -> do
        forM_ hs $ \(h, i) -> do
          mkProof i >> tell (Endo (PCHyp :))
          (_, heap) <- ask
          case h >>= flip H.lookup heap . PHypE of
            Nothing -> modify $ mapFst (+1)
            Just k -> pushHeap k
        mkProof ret

  writeIndex :: ExportM ()
  writeIndex = do
    let headerLen = 8 * (1 +
          V.length (mArr sorts) + V.length (mArr terms) + V.length (mArr thms))
    revision fixup (fromIntegral headerLen) $
      (,) () <$> runStateT (writeIndex' $ buildIndex [] (M.size nameTree, nameTree)) def
    where
    fixup (pRoot, (pSorts, pTerms, pIndex)) = do
      writeU64 pRoot >> mapM_ writeU64 pSorts >> mapM_ writeU64 pTerms >> mapM_ writeU64 pIndex

    nameTree :: M.Map Ident (NE.NonEmpty Name)
    nameTree = go thms ThmName $ go terms TermName $ go sorts SortName M.empty where
      go :: Mapping a -> (Ident -> Name) ->
        M.Map Ident (NE.NonEmpty Name) -> M.Map Ident (NE.NonEmpty Name)
      go ix f = flip (V.foldl' $ \m (x, _) ->
        M.alter (Just . (f x NE.:|) . maybe [] NE.toList) x m) (mArr ix)

    buildIndex :: [Name] -> (Int, M.Map Ident (NE.NonEmpty Name)) -> Index
    buildIndex ns (0, _) = go ns where
      go [] = INil
      go (n : ns') = INode (buildEntry n) INil (go ns')
    buildIndex ns (len, m) =
      let i = len `div` 2
          (left, right') = M.splitAt i m
          ((_, n NE.:| ns2), right) = M.deleteFindMin right' in
      INode (buildEntry n) (buildIndex ns (i, left))
        (buildIndex ns2 (len - i - 1, right))

    buildEntry :: Name -> IEntry
    buildEntry n = IEntry n (ix n) 0 0 where
      ix (SortName x) = mIx sorts M.! x
      ix (TermName x) = mIx terms M.! x
      ix (ThmName x) = mIx thms M.! x

    writeIndex' :: Index -> IndexM Word64
    writeIndex' INil = return 0
    writeIndex' (INode (IEntry n ix row col) l r) = do
      il <- writeIndex' l
      ir <- writeIndex' r
      pos <- lift $ alignTo 8 >> get
      f <- lift $ do
        writeU64 il
        writeU64 ir
        writeU32 row
        writeU32 col
        writeU64 0 -- TODO: pointer to command
        writeU32 $ fromIntegral ix
        let (x, k, f) = mkKind ix pos n
        writeU8 k
        writeBS (T.encodeUtf8 x) >> writeU8 0
        return f
      fromIntegral pos <$ modify f

    mkKind :: Int -> Word64 -> Name -> (Ident, Word8, PMapping -> PMapping)
    mkKind ix p (SortName x) = (x, 0x04, \(a, b, c) -> (I.insert ix p a, b, c))
    mkKind ix p (TermName x) =
        (x, go (mArr terms V.! ix), \(a, b, c) -> (a, I.insert ix p b, c)) where
      go (_, TermData _ _ _ Nothing)              = 0x01
      go (_, TermData Local _ _ _)                = 0x0D
      go (_, TermData _ _ _ _)                    = 0x05
    mkKind ix p (ThmName x) =
        (x, go (mArr thms V.! ix), \(a, b, c) -> (a, b, I.insert ix p c)) where
      go (_, ThmData _ _ (ProofStmt _ _ Nothing)) = 0x02
      go (_, ThmData Public _ _)                  = 0x06
      go (_, ThmData _ _ _)                       = 0x0E

type ExportM = RWST () BB.Builder Word64 (Either String)

flag :: Num a => Bool -> a -> a
flag False _ = 0
flag True n = n

revision :: (a -> ExportM ()) -> Word64 -> ExportM (r, a) -> ExportM r
revision f n m = RWST $ \() ix -> do
  ((r, a), ix', w') <- runRWST m () (ix + n)
  ((), ix2, w) <- runRWST (f a) () ix
  unless (ix2 == ix + n) $ error "index mismatch"
  return (r, ix', w <> w')

fixup32 :: ExportM (r, Word32) -> ExportM r
fixup32 = revision writeU32 4

fixup64 :: ExportM (r, Word64) -> ExportM r
fixup64 = revision writeU64 8

writeBS :: BS.ByteString -> ExportM ()
writeBS s = tell (BB.fromByteString s) >> modify (+ fromIntegral (BS.length s))

alignTo :: Int -> ExportM ()
alignTo n = get >>= \ix -> padN $ fromIntegral ((-ix) `mod` fromIntegral n)

padN :: Int -> ExportM ()
padN n = tell (BB.fromByteString (BS.replicate n 0)) >> modify (+ fromIntegral n)

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
  | UHyp
  deriving (Show)

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
writeUnifyCmd UHyp          = writeU8 0x36

-- writeUnifyCmd' :: UnifyCmd -> ExportM ()
-- writeUnifyCmd' c = do
--   ix <- get <* writeUnifyCmd c
--   traceM ("  " ++ showHex ix (": " ++ show c))

writeUnify :: [UnifyCmd] -> ExportM ()
writeUnify l = mapM writeUnifyCmd l >> writeU8 0

data ProofCmd =
    PCTerm Word32
  | PCTermSave Word32
  | PCRef Word32
  | PCDummy Word32 Ident
  | PCThm Word32
  | PCThmSave Word32
  | PCHyp
  | PCConv
  | PCRefl
  | PCSym
  | PCCong
  | PCUnfold
  | PCConvCut
  | PCConvRef Word32
  deriving (Show)

writeProofCmd :: ProofCmd -> ExportM ()
writeProofCmd (PCTerm n)     = writeCmd 0x10 n
writeProofCmd (PCTermSave n) = writeCmd 0x11 n
writeProofCmd (PCRef n)      = writeCmd 0x12 n
writeProofCmd (PCDummy n _)  = writeCmd 0x13 n
writeProofCmd (PCThm n)      = writeCmd 0x14 n
writeProofCmd (PCThmSave n)  = writeCmd 0x15 n
writeProofCmd PCHyp          = writeU8 0x16
writeProofCmd PCConv         = writeU8 0x17
writeProofCmd PCRefl         = writeU8 0x18
writeProofCmd PCSym          = writeU8 0x19
writeProofCmd PCCong         = writeU8 0x1A
writeProofCmd PCUnfold       = writeU8 0x1B
writeProofCmd PCConvCut      = writeU8 0x1C
writeProofCmd (PCConvRef n)  = writeCmd 0x1D n

-- writeProofCmd' :: ProofCmd -> ExportM ()
-- writeProofCmd' c = do
--   ix <- get <* writeProofCmd c
--   traceM ("  " ++ showHex ix (": " ++ show c))

writeProof :: [ProofCmd] -> ExportM ()
writeProof l = mapM writeProofCmd l >> writeU8 0

data Index = INil | INode IEntry Index Index

data IEntry = IEntry {
  _ieKey :: Name,
  _ieIx :: Int,
  _ieRow :: Word32,
  _ieCol :: Word32 }
