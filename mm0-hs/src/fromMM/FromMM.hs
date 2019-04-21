module FromMM (fromMM, showBundled) where

import System.IO
import System.Exit
import System.Environment
import Control.Monad.State hiding (liftIO)
import Control.Monad.RWS.Strict hiding (liftIO)
import Control.Monad.Except hiding (liftIO)
import Data.Foldable
import Data.Maybe
import Debug.Trace
import Text.Printf
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString.Char8 as C
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Q
import qualified Data.IntMap as I
import qualified Data.Set as S
import Util
import MMTypes
import MMParser
import FindBundled
import Environment (Ident, DepType(..), SortData(..), SExpr(..))
import ProofTypes
import qualified AST as A

write :: String -> (Handle -> IO ()) -> IO ()
write f io = withFile f WriteMode $ \h ->
  hSetNewlineMode h (NewlineMode LF LF) >> io h

showBundled :: [String] -> IO ()
showBundled [] = die "show-bundled: no .mm file specified"
showBundled (mm : _) = do
  db <- withFile mm ReadMode $ \h ->
    B.hGetContents h >>= liftIO . parseMM
  putStrLn $ show (M.size (findBundled db)) ++ " bundled theorems, " ++
    show (sum (S.size <$> toList (findBundled db))) ++ " total copies"
  mapM_ (\(l, s) -> putStrLn $ padL 15 l ++ "  " ++ show (S.toList s)) $
    mapMaybe (\case
      Stmt s -> (,) s <$> (findBundled db M.!? s)
      _ -> Nothing) (toList (mDecls db))

fromMM :: [String] -> IO ()
fromMM [] = die "from-mm: no .mm file specified"
fromMM (mm : rest) = do
  db <- withFile mm ReadMode $ \h ->
    B.hGetContents h >>= liftIO . parseMM
  (mm0, mmu) <- case rest of
    [] -> return (\k -> k stdout, \k -> k (\_ -> return ()))
    "-o" : mm0 : [] -> return (write mm0, \k -> k (\_ -> return ()))
    "-o" : mm0 : mmu : _ -> return (write mm0, \k -> write mmu $ k . hPutStrLn)
    _ -> die "from-mm: too many arguments"
  mm0 $ \h -> mmu $ printAST db (hPutStrLn h)

withContext :: MonadError String m => String -> m a -> m a
withContext s m = catchError m (\e -> throwError ("at " ++ s ++ ": " ++ e))

data ParseTrie = PT {
  ptConst :: Parser,
  ptVar :: M.Map Sort ParseTrie,
  ptDone :: Maybe (Sort, [MMExpr] -> MMExpr) }
type Parser = M.Map Const ParseTrie

type MMExpr = SExpr

ptEmpty :: ParseTrie
ptEmpty = PT M.empty M.empty Nothing

ptInsert :: M.Map Var (Sort, Ident) -> ([MMExpr] -> MMExpr) -> Fmla -> Parser -> Parser
ptInsert vm x (Const s : f) = insert1 s f where
  insert1 :: String -> [Sym] -> Parser -> Parser
  insert1 i f = M.alter (Just . insertPT f . fromMaybe ptEmpty) i
  insertPT :: [Sym] -> ParseTrie -> ParseTrie
  insertPT [] (PT cs vs Nothing) = PT cs vs (Just (s, x))
  insertPT [] (PT _ _ _) = error "duplicate parser"
  insertPT (Const c : f) (PT cs vs d) = PT (insert1 c f cs) vs d
  insertPT (Var v : f) (PT cs vs d) =
    PT cs (insert1 (fst (vm M.! v)) f vs) d
ptInsert _ _ _ = error "bad decl"

reorderMap :: M.Map Var Int -> Fmla -> [MMExpr] -> [MMExpr]
reorderMap m f = let l = I.elems (buildIM f 0 I.empty) in \es -> map (es !!) l where
  buildIM :: Fmla -> Int -> I.IntMap Int -> I.IntMap Int
  buildIM [] _ i = i
  buildIM (Const _ : f) n i = buildIM f n i
  buildIM (Var v : f) n i = buildIM f (n+1) (I.insert (m M.! v) n i)

data TransState = TransState {
  tParser :: Parser,
  tVMap :: M.Map Var (Sort, Label),
  tParsedHyps :: M.Map Label MMExpr,
  tNameMap :: M.Map Label Ident,
  tUsedNames :: S.Set Ident,
  tBuilders :: M.Map Label (Maybe ([VExpr] -> VExpr), [ProofTree] -> ProofTree),
  tIxLookup :: IxLookup }

mkTransState :: TransState
mkTransState = TransState M.empty M.empty M.empty M.empty S.empty M.empty mkIxLookup

type TransM = RWST (MMDatabase, M.Map Label Bundles)
  (Endo [String]) TransState (Either String)

runTransM :: TransM a -> MMDatabase -> Either String a
runTransM m db = fst <$> evalRWST m (db, findBundled db) mkTransState

makeAST :: MMDatabase -> Either String (A.AST, Proofs)
makeAST db = trDecls (mDecls db)
  (A.Notation (A.Delimiter $ A.Const $ C.pack " ( ) ") :) id mkTransState where
  init = (db, findBundled db)
  trDecls :: Q.Seq Decl -> (A.AST -> A.AST) -> (Proofs -> Proofs) ->
    TransState -> Either String (A.AST, Proofs)
  trDecls Q.Empty f g s = return (f [], g [])
  trDecls (d Q.:<| ds) f g st = runRWST (trDecl () d) init st >>= \case
    (Nothing, st', _) -> trDecls ds f g st'
    (Just (d, p), st', _) -> trDecls ds (f . (d :)) (g . (p :)) st'

printAST :: MMDatabase -> (String -> IO ()) -> (String -> IO ()) -> IO ()
printAST db mm0 mmu = do
  mm0 $ shows (A.Notation $ A.Delimiter $ A.Const $ C.pack " ( ) ") "\n"
  trDecls (mDecls db) mkTransState mkSeqPrinter
  where
  init = (db, findBundled db)
  trDecls :: Q.Seq Decl -> TransState -> SeqPrinter -> IO ()
  trDecls Q.Empty s p = return ()
  trDecls (d Q.:<| ds) st p = liftIO (runRWST (trDecl p d) init st) >>= \case
      (Nothing, st', w) -> report w >> trDecls ds st' p
      (Just (a, pf), st', w) -> do
        let (s, p') = ppProofCmd' p pf
        mm0 $ shows a "\n"
        mmu $ s "\n"
        report w
        trDecls ds st' p'

  report :: Endo [String] -> IO ()
  report (Endo f) = mapM_ (hPutStrLn stderr) (f [])

-- fromJust' :: String -> Maybe a -> a
-- fromJust' _ (Just a) = a
-- fromJust' s Nothing = error $ "fromJust: " ++ s

-- (<!>) :: (HasCallStack, Ord k, Show k, Show v) => M.Map k v -> k -> v
-- (<!>) m k = case m M.!? k of
--   Nothing -> error $ show m ++ " ! " ++ show k
--   Just v -> v

report :: a -> TransM a -> TransM a
report a m = catchError m (\e -> tell (Endo (e :)) >> return a)

type ParseResult = [(([MMExpr] -> [MMExpr]) -> MMExpr, [Sym])]
parseFmla :: Fmla -> TransM MMExpr
parseFmla = \case
  Const s : f -> do
    t <- get
    (db, _) <- ask
    let s2 = fromMaybe s (fst $ mSorts db M.! s)
    fromJustError (error ("cannot parse formula " ++ show (Const s : f)))
      (parseFmla' (tVMap t) (tParser t) s2 f)
  f -> error ("bad formula" ++ show f)
  where
  parseFmla' :: M.Map Var (Sort, Label) -> Parser -> Sort -> [Sym] -> Maybe MMExpr
  parseFmla' vm p = \s f -> parseEOF (parse s p f) where
    parseEOF :: [(MMExpr, [Sym])] -> Maybe MMExpr
    parseEOF [] = Nothing
    parseEOF ((e, []) : _) = Just e
    parseEOF (_ : es) = parseEOF es
    parse :: Sort -> Parser -> [Sym] -> [(MMExpr, [Sym])]
    parse s p f = (case f of
      Var v : f' -> let (s', v') = vm M.! v in
        if s == s' then [(SVar v', f')] else []
      _ -> []) ++ ((\(g, f') -> (g id, f')) <$> parseC s p s f)
    parseC :: Sort -> Parser -> Const -> [Sym] -> ParseResult
    parseC s q c f = parsePT s f (M.findWithDefault ptEmpty c q)
    parseD :: Sort -> Maybe (Sort, [MMExpr] -> MMExpr) -> [Sym] -> ParseResult
    parseD s (Just (s', i)) f | s' == s = [(\g -> i (g []), f)]
    parseD s d f = []
    parsePT :: Sort -> [Sym] -> ParseTrie -> ParseResult
    parsePT s f (PT cs vs d) = (case f of
      Const c : f' -> parseC s cs c f'
      _ -> []) ++ parseV s vs f ++ parseD s d f
    parseV :: Sort -> M.Map Sort ParseTrie -> [Sym] -> ParseResult
    parseV s vs f = M.foldrWithKey parseV1 [] vs where
      parseV1 :: Sort -> ParseTrie -> ParseResult -> ParseResult
      parseV1 s' q r = (do
        (v, f') <- parse s' p f
        (g, f'') <- parsePT s f' q
        [(g . (. (v :)), f'')]) ++ r

trDecl :: IDPrinter a => a -> Decl -> TransM (Maybe (A.Stmt, ProofCmd))
trDecl a d = ask >>= \(db, _) -> case d of
  Sort s -> case mSorts db M.! s of
    (Nothing, sd) -> do
      i <- trName s (mangle s)
      modify $ \m -> m {tIxLookup = ilInsertSort s (tIxLookup m)}
      return $ Just (A.Sort i sd, StepSort i)
    _ -> return Nothing
  Stmt st -> case mStmts db M.! st of
    Hyp (VHyp c v) -> do
      trName st (if identStr v then v else mangle st)
      modify $ \m -> m {
        tVMap = M.insert v (c, st) (tVMap m),
        tParsedHyps = M.insert st (SVar v) (tParsedHyps m) }
      return Nothing
    Hyp (EHyp f) -> do
      e <- parseFmla f
      modify $ \m -> m {tParsedHyps = M.insert st e (tParsedHyps m)}
      return Nothing
    Thm fr f@(Const s : _) p -> case mSorts db M.! s of
      (Nothing, _) -> case p of
        Nothing -> do
          (bs1, _, _, reord, rm) <- splitFrame fr
          i <- trName st (mangle st)
          let g = App st . reorderMap reord f
          modify $ \m ->
            let lup = tIxLookup m
                n = fst (pTermIx lup)
                bd es = VTerm (TermID n) (map (es !!) rm)
                be es = VApp (TermID n) (map (es !!) rm) in
            m {
              tParser = ptInsert (tVMap m) g f (tParser m),
              tBuilders = M.insert st (Just be, bd) (tBuilders m),
              tIxLookup = ilInsertTerm st $ ilResetVars lup }
          return $ Just (A.Term i bs1 (DepType s []), StepTerm i)
        Just p -> do
          t <- get
          (be, bd) <- lift $ withContext st $ trSyntaxProof fr t p
          modify $ \m -> m {tBuilders = M.insert st (Just be, bd) (tBuilders m)}
          return Nothing
      (Just _, _) -> do
        (bs1, bs2, hs2, _, rm) <- splitFrame fr
        (e1, e2) <- parseFmla f >>= trExpr
        i <- trName st (mangle st)
        ret <- case p of
          Nothing -> return (A.Axiom i bs1 (exprToFmla e1), StepAxiom i)
          Just p -> do
            t <- get
            let (ds, pr) = trProof fr t p
            return (A.Theorem i bs1 (exprToFmla e1),
              ProofThm (Just i) bs2 hs2 e2 [] ds pr True)
        modify $ \m ->
          let lup = tIxLookup m
              n = fst (pThmIx lup)
              bd es = VThm (ThmID n) (map (es !!) rm) in
          m {
            tBuilders = M.insert st (Nothing, bd) (tBuilders m),
            tIxLookup = ilInsertThm st $ ilResetVars lup }
        return $ Just ret
    Thm _ _ _ -> throwError "bad theorem statement"

splitFrame :: Frame -> TransM ([A.Binder], [VBinder], [VExpr], M.Map Var Int, [Int])
splitFrame (hs, ds) = do (db, _) <- ask; splitFrame' hs ds db
splitFrame' hs ds db = do
  (vs, bs, hs', f) <- partitionHyps hs 0
  (bs1, bs2, hs2) <- processArgs vs bs hs'
  return (bs1, bs2, hs2, buildReorder (vs ++ bs) 0 M.empty,
    I.elems (f 0 (length vs) (length vs + length bs)))
  where

  partitionHyps :: [(Bool, Label)] -> Int -> TransM ([(Var, Label, Sort)],
    [(Var, Label, Sort)], [Label], Int -> Int -> Int -> I.IntMap Int)
  partitionHyps [] _ = return ([], [], [], \_ _ _ -> I.empty)
  partitionHyps ((b, l) : ls) li = case mStmts db M.! l of
    Hyp (VHyp s v) -> do
      (vs, bs, hs', f) <- partitionHyps ls (li+1)
      if b then return ((v, l, s) : vs, bs, hs',
        \vi bi hi -> I.insert vi li (f (vi+1) bi hi))
      else return (vs, (v, l, s) : bs, hs',
        \vi bi hi -> I.insert bi li (f vi (bi+1) hi))
    Hyp (EHyp _) -> do
      (vs, bs, hs, f) <- partitionHyps ls (li+1)
      return (vs, bs, l : hs,
        \vi bi hi -> I.insert hi li (f vi bi (hi+1)))

  processArgs :: [(Var, Label, Sort)] -> [(Var, Label, Sort)] -> [Label] ->
    TransM ([A.Binder], [VBinder], [VExpr])
  processArgs vs bs hs = processBound vs where
    processBound :: [(Var, Label, Sort)] -> TransM ([A.Binder], [VBinder], [VExpr])
    processBound [] = processReg bs
    processBound ((_, l, s) : vs) = do
      modify $ \g -> g {tIxLookup = ilInsertVar l (tIxLookup g)}
      (bs1, bs2, hs') <- processBound vs
      t <- get
      let v' = tNameMap t M.! l
      let s' = tNameMap t M.! s
      let s2 = fromJust $ ilSort (tIxLookup t) s
      return (A.Binder (A.LBound v') (A.TType $ DepType s' []) : bs1,
        VBound s2 : bs2, hs')

    processReg :: [(Var, Label, Sort)] -> TransM ([A.Binder], [VBinder], [VExpr])
    processReg [] = do (hs1, hs2) <- processHyps hs; return (hs1, [], hs2)
    processReg ((v, l, s) : bs) = do
      modify $ \g -> g {tIxLookup = ilInsertVar l (tIxLookup g)}
      (bs1, bs2, hs2) <- processReg bs
      t <- get
      let v' = tNameMap t M.! l
      let s' = tNameMap t M.! s
      let s2 = fromJust $ ilSort (tIxLookup t) s
      let f (v2, l2, _) = if memDVs ds v v2 then Nothing else
            Just (tNameMap t M.! l2, fromJust $ ilVar (tIxLookup t) l2)
          (vs1, vs2) = unzip $ mapMaybe f vs
      return (A.Binder (A.LReg v') (A.TType $ DepType s' vs1) : bs1,
        VReg s2 vs2 : bs2, hs2)

    processHyps :: [Label] -> TransM ([A.Binder], [VExpr])
    processHyps [] = return ([], [])
    processHyps (l : ls) = do
      modify $ \t -> t {tIxLookup = ilInsertVar l (tIxLookup t)}
      (hs1, hs2) <- processHyps ls
      t <- get
      (e1, e2) <- trExpr (tParsedHyps t M.! l)
      i <- trName l (mangle l)
      return (A.Binder (A.LReg i) (A.TFormula $ exprToFmla e1) : hs1, e2 : hs2)

  buildReorder :: [(Var, Label, Sort)] -> Int -> M.Map Var Int -> M.Map Var Int
  buildReorder [] n m = m
  buildReorder ((v, _, _):vs) n m = buildReorder vs (n+1) (M.insert v n m)

trName :: Label -> Ident -> TransM Ident
trName lab name = get >>= \m -> case tNameMap m M.!? lab of
  Just s -> return s
  Nothing -> alloc (tUsedNames m) (name : ((\n -> name ++ show n) <$> [1..]))
  where
  alloc :: S.Set Ident -> [String] -> TransM Ident
  alloc used (n : ns) | S.member n used = alloc used ns
  alloc used (n : _) = do
    modify $ \m -> m {
      tNameMap = M.insert lab n (tNameMap m),
      tUsedNames = S.insert n (tUsedNames m) }
    return n

trExpr :: MMExpr -> TransM (SExpr, VExpr)
trExpr e = (\t -> trExpr' (tNameMap t) (tIxLookup t) e) <$> get

trExpr' :: M.Map Label Ident -> IxLookup -> MMExpr -> (SExpr, VExpr)
trExpr' names lup = go where
  go (SVar v) = (SVar (names M.! v), VVar (fromJust $ ilVar lup v))
  go (App t es) = let (es1, es2) = unzip (go <$> es) in
    (App (names M.! t) es1, VApp (fromJust $ ilTerm lup t) es2)

exprToFmla :: SExpr -> A.Formula
exprToFmla e = A.Formula $ C.pack $ ' ' : showsPrec 0 e " "

identCh1 :: Char -> Bool
identCh1 c = 'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' || c == '_'

identCh :: Char -> Bool
identCh c = '0' <= c && c <= '9' || identCh1 c

identStr :: String -> Bool
identStr [] = False
identStr "_" = False
identStr (c:s) = identCh1 c && all identCh s

mangle :: String -> Ident
mangle "" = "null"
mangle (c : s) =
  if identCh1 c then c : map mangle1 s
  else '_' : map mangle1 (c : s) where
  mangle1 c = if identCh c then c else '_'

data HeapEl = HeapEl HeapID | HBuild (Int, [ProofTree] -> ProofTree)

ppHeapEl :: IDPrinter a => a -> HeapEl -> String
ppHeapEl a (HeapEl n) = ppVar a n
ppHeapEl a (HBuild (_, f)) = case f [] of
  VTerm n _ -> ppTerm a n
  VThm n _ -> ppThm a n

instance Show HeapEl where show = ppHeapEl ()

trProof :: Frame -> TransState ->
  ([Label], Proof) -> ([SortID], ProofTree)
trProof (hs, _) t (ds, pr) = (fromJust . ilSort lup <$> ds, trProof' pr) where
  lup = tIxLookup t
  nhs = length hs
  nds = length ds

  trProof' :: Proof -> ProofTree
  trProof' (PHyp v _) = Load $ fromJust $ ilVar lup v
  trProof' (PDummy n) = Load $ VarID (nhs + n)
  trProof' (PBackref n) = Load $ VarID (nhs + nds + n)
  trProof' PSorry = Sorry
  trProof' (PSave p) = Save (trProof' p)
  trProof' (PThm st ps) = snd (tBuilders t M.! st) (trProof' <$> ps)

trSyntaxProof :: Frame -> TransState -> ([Label], Proof) ->
  Either String ([VExpr] -> VExpr, [ProofTree] -> ProofTree)
trSyntaxProof (hs, _) t (ds, pr) = do
  guardError "dummy variable in syntax proof" (null ds)
  e <- evalStateT (toExpr pr) Q.empty
  return (substExpr e, substProof e) where

  toExpr :: Proof -> StateT (Q.Seq VExpr) (Either String) VExpr
  toExpr (PHyp _ v) = return (VVar (VarID v))
  toExpr (PDummy n) = throwError "dummy variable in syntax proof"
  toExpr (PBackref n) = (\s -> Q.index s n) <$> get
  toExpr PSorry = throwError "? in syntax proof"
  toExpr (PSave p) = do e <- toExpr p; state (\s -> (e, s Q.|> e))
  toExpr (PThm st ps) = do
    ps' <- mapM toExpr ps
    be <- fromJustError "theorem used in syntax proof" (fst (tBuilders t M.! st))
    return (be ps')

  substExpr :: VExpr -> [VExpr] -> VExpr
  substExpr e es = go e where
    go (VVar (VarID n)) = es !! n
    go (VApp t es') = VApp t (go <$> es')

  substProof :: VExpr -> [ProofTree] -> ProofTree
  substProof e es = go e where
    go (VVar (VarID n)) = es !! n
    go (VApp t ps) = VTerm t (go <$> ps)
