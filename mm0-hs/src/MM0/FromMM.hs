module MM0.FromMM (fromMM, showBundled) where

import System.IO
import System.Exit
import Control.Monad.State
import Control.Monad.RWS.Strict
import Data.Foldable
import Data.Maybe
import Data.Default
import qualified Data.ByteString.Lazy as B
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Q
import qualified Data.IntMap as I
import qualified Data.Set as S
import qualified Data.Text as T
import MM0.Util
import MM0.FromMM.Types
import MM0.FromMM.Parser
import MM0.FromMM.Emancipate
import MM0.FromMM.Closure
import MM0.FromMM.FindBundled
import MM0.Kernel.Environment (Ident, DepType(..), SExpr(..))
import MM0.Kernel.Types
import qualified MM0.FrontEnd.AST as A

write :: String -> (Handle -> IO ()) -> IO ()
write f io = withFile f WriteMode $ \h ->
  hSetNewlineMode h (NewlineMode LF LF) >> io h

showBundled :: [String] -> IO ()
showBundled [] = die "show-bundled: no .mm file specified"
showBundled (mm : rest) = do
  db <- withFile mm ReadMode $ \h ->
    B.hGetContents h >>= liftIO' . parseMM
  let db' = emancipate db
  let bu = findBundled db'
  case rest of
    [] -> showBundles db bu
    "-r" : n : _ -> do
      let bu' = filt (\_ _ i -> i <= read n) bu
      let s = reportBundled db' bu'
      forM_ s $ \((x, o), (t, b)) ->
        putStrLn ("theorem " ++ T.unpack x ++ maybe "" show o ++ " references " ++ T.unpack t ++ show b)
      putStrLn ""
      let s' = S.map fst s
      showBundles db $ filt (\x i _ -> S.member (x, Just i) s') bu'
    n : _ -> showBundles db $ filt (\_ _ i -> i <= read n) bu
  where
  filt :: (Label -> [Int] -> Int -> Bool) -> M.Map Label Bundles -> M.Map Label Bundles
  filt f = M.filter (not . M.null) . M.mapWithKey (\x -> M.filterWithKey (f x))

  showBundles :: MMDatabase -> M.Map Label Bundles -> IO ()
  showBundles db bu = out $ mapMaybe (\case
    Stmt x -> do
      s' <- bu M.!? x
      if M.null s' then Nothing else Just (x, fst <$> M.toList s')
    _ -> Nothing) (toList (mDecls db))

  out :: [(Label, [[Int]])] -> IO ()
  out ls = do
    putStrLn $ show (length ls) ++ " bundled theorems, " ++
      show (sum (length . snd <$> ls)) ++ " total copies"
    mapM_ (\(l, s) -> putStrLn $ padL 15 (T.unpack l) ++ "  " ++ show s) ls

fromMM :: [String] -> IO ()
fromMM [] = die "from-mm: no .mm file specified"
fromMM (mm : rest) = do
  db <- withFile mm ReadMode $ \h ->
    B.hGetContents h >>= liftIO' . parseMM
  let db' = emancipate db
  (dbf, rest') <- return $ case rest of
    "-f" : l : rest' ->
      let {ls = T.splitOn "," (T.pack l); (ss, sl) = closure db' ls} in
      (Just (ss, sl, S.fromList ls), rest')
    _ -> (Nothing, rest)
  (mm0, mmu) <- case rest' of
    [] -> return (\k -> k stdout, \k -> k (\_ -> return ()))
    "-o" : mm0 : [] -> return (write mm0, \k -> k (\_ -> return ()))
    "-o" : mm0 : mmu : _ -> return (write mm0, \k -> write mmu $ k . hPutStrLn)
    _ -> die "from-mm: too many arguments"
  mm0 $ \h -> mmu $ printAST db' dbf (hPutStrLn h)

data DBInfo = DBInfo {
  dbiF :: DBFilter,
  dbiBundles :: M.Map Label Bundles,
  _dbiDefs :: M.Map Label Label }

type DBFilter = Maybe (S.Set Sort, S.Set Label, S.Set Label)

sortMember :: DBInfo -> Sort -> Bool
sortMember i x = all (\(s, _, _) -> S.member x s) (dbiF i)

stmtMember :: DBInfo -> Label -> Bool
stmtMember i x = all (\(_, s, _) -> S.member x s) (dbiF i)

stmtPublic :: DBInfo -> Label -> Bool
stmtPublic i x = all (\(_, _, s) -> S.member x s) (dbiF i)

data Builder = Builder {
  bExpr :: Maybe ([Int], [VExpr] -> VExpr),
  bProof :: [ProofTree] -> ProofTree }

data TransState = TransState {
  tNameMap :: M.Map Label Ident,
  tBNameMap :: M.Map (Label, [Int]) Ident,
  tUsedNames :: S.Set Ident,
  tBuilders :: M.Map Label Builder,
  tIxLookup :: IxLookup }

instance Default TransState where
  def = TransState def def def def def

type TransM = RWST (MMDatabase, DBInfo)
  (Endo [String]) TransState (Either String)

runTransM :: TransM a -> MMDatabase -> DBFilter -> TransState -> Either String (a, TransState, [String])
runTransM m db dbf st = do
  let i = DBInfo dbf (findBundled db) (findDefinitions db)
  (os, st', Endo w) <- runRWST m (db, i) st
  return (os, st', w [])

_makeAST :: MMDatabase -> DBFilter -> Either String (A.AST, Proofs)
_makeAST db dbf = trDecls (mDecls db)
  (A.Notation (A.Delimiter $ A.Const $ T.pack " ( ) ") :) id def where
  trDecls :: Q.Seq Decl -> (A.AST -> A.AST) -> (Proofs -> Proofs) ->
    TransState -> Either String (A.AST, Proofs)
  trDecls Q.Empty f g _ = return (f [], g [])
  trDecls (d Q.:<| ds) f g st = do
    (os, st', _) <- runTransM (trDecl d) db dbf st
    let (ds', ps) = unzip os
    trDecls ds (f . (catMaybes ds' ++)) (g . (ps ++)) st'

printAST :: MMDatabase -> DBFilter -> (String -> IO ()) -> (String -> IO ()) -> IO ()
printAST db dbf mm0 mmu = do
  mm0 $ shows (A.Notation $ A.Delimiter $ A.Const $ T.pack " ( ) ") "\n"
  trDecls (mDecls db) def def
  where
  trDecls :: Q.Seq Decl -> TransState -> SeqPrinter -> IO ()
  trDecls Q.Empty _ _ = return ()
  trDecls (d Q.:<| ds) st p = do
    (os, st', w) <- liftIO' (runTransM (trDecl d) db dbf st)
    p' <- foldlM (\p1 (a, pf) -> do
      let (s, p') = ppProofCmd' p1 pf
      forM_ a $ \a' -> mm0 $ shows a' "\n"
      mmu $ s "\n"
      return p') p os
    mapM_ (hPutStrLn stderr) w
    trDecls ds st' p'

-- fromJust' :: String -> Maybe a -> a
-- fromJust' _ (Just a) = a
-- fromJust' s Nothing = error $ "fromJust: " ++ s

-- (<!>) :: (HasCallStack, Ord k, Show k) => M.Map k v -> k -> v
-- (<!>) m k = case m M.!? k of
--   Nothing -> error $ show (M.keys m) ++ " ! " ++ show k
--   Just v -> v

reorder :: [Int] -> [a] -> [a]
reorder ns l = (l !!) <$> ns

trDecl :: Decl -> TransM [(Maybe A.Stmt, ProofCmd)]
trDecl d = get >>= \t -> ask >>= \(db, i) -> case d of
  Sort s -> if sortMember i s then
    case mSorts db M.! s of
      (Nothing, sd) -> do
        st' <- trName s (mangle s)
        modify $ \m -> m {tIxLookup = ilInsertSort s (tIxLookup m)}
        return [(Just $ A.Sort st' sd, StepSort st')]
      _ -> return []
    else return []
  Stmt st -> if stmtMember i st && M.notMember st (tNameMap t) then
    case getStmt db st of
      (_, Hyp (VHyp _ v)) ->
        trName st (if identStr v then v else mangle st) >> return []
      (_, Hyp (EHyp _ _)) -> return []
      (ix, Term fr (s, _) Nothing) -> trDefinition ix st >>= \case
        [] -> do
          splitFrame Nothing fr $ \(SplitFrame bs1 _ _ _ rm _) -> do
            st' <- trName st (mangle st)
            modify $ \m ->
              let {lup = tIxLookup m; n = TermID (fst (pTermIx lup))} in
              m {
                tBuilders = M.insert st
                  (Builder (Just (rm, VApp n)) (VTerm n . reorder rm))
                  (tBuilders m),
                tIxLookup = ilInsertTerm st lup }
            return [(Just $ A.Term st' bs1 (DepType s []), StepTerm st')]
        e -> return e
      (_, Term fr (_, e) (Just _)) -> splitFrame Nothing fr $ \sf -> do
        let rm = sfReord sf
        (_, e2) <- trExpr id e
        let (be, bd) = trSyntaxProof e2
        modify $ \t' -> t' {
          tBuilders = M.insert st
            (Builder (Just (rm, be)) (bd . reorder rm)) (tBuilders t') }
        return []
      (_, Thm fr e p) -> do
        let mst = mangle st
        let pub = stmtPublic i st
        (out, n, pa, rm) <- trName st mst >>= trThmB Nothing pub fr e p
        (out2, ns) <- unzip <$> mapM (\bu -> do
          (out', n', _, rm') <-
            trBName st bu (mst <> "_b") >>= trThmB (Just bu) pub fr e p
          return (out', (bu, (n', rm'))))
          (maybe [] M.keys (dbiBundles i M.!? st))
        modify $ \t' -> t' {tBuilders = M.insert st (mkThmBuilder pa rm n ns) (tBuilders t')}
        return (out : out2)
      (_, Alias _) -> return []
    else return []

trThmB :: Maybe [Int] -> Bool -> Frame -> (Const, MMExpr) -> Maybe ([Label], Proof) ->
  Ident -> TransM ((Maybe A.Stmt, ProofCmd), ThmID, [Int], [Int])
trThmB bu pub fr (_, e) p i =
  splitFrame bu fr $ \(SplitFrame bs1 bs2 hs2 pa rm vm) -> do
    (e1, e2) <- trExpr vm e
    ret <- case p of
      Nothing -> return (Just $ A.Axiom i bs1 (exprToFmla e1), StepAxiom i)
      Just p' -> do
        t <- get
        let (ds, pr) = trProof vm (length bs1) t p'
        return (
          if pub then Just $ A.Theorem i bs1 (exprToFmla e1) else Nothing,
          ProofThm (Just i) bs2 hs2 e2 [] ds pr pub)
    state $ \t ->
      let lup = tIxLookup t
          n = ThmID (fst (pThmIx lup)) in
      ((ret, n, pa, rm), t {tIxLookup = ilInsertThm i lup})

mkThmBuilder :: [Int] -> [Int] -> ThmID -> [([Int], (ThmID, [Int]))] -> Builder
mkThmBuilder _ rm n [] = Builder Nothing (VThm n . reorder rm)
mkThmBuilder pa rm n ns = let m = M.fromList ns in
  Builder Nothing $ \ps ->
    let vs = (\(Load v) -> v) <$> reorder pa ps in
    if allUnique vs then VThm n (reorder rm ps) else
      let {bu = bundle vs; (t, rm') = m M.! bu} in
      VThm t (reorder rm' ps)

data SplitFrame = SplitFrame {
  _sfBound :: [A.Binder],
  _sfVBound :: [VBinder],
  _sfHyps :: [VExpr],
  _sfPureArgs :: [Int],
  sfReord :: [Int],
  _sfVarmap :: Label -> Label }

splitFrame :: Maybe [Int] -> Frame -> (SplitFrame -> TransM a) -> TransM a
splitFrame bu (hs, dv) k = do
  a <- ask >>= splitFrame' bu hs dv . fst >>= k
  modify $ \t -> t {tIxLookup = ilResetVars (tIxLookup t)}
  return a
splitFrame' :: Maybe [Int] -> [(VarStatus, Label)] -> DVs ->
  MMDatabase -> TransM SplitFrame
splitFrame' bu hs dv db = do
  let (vs1, pa) = filterPos (vsPure . fst) hs
  let vs' = invertB bu vs1
  let vm = mkVarmap bu (snd <$> vs1) vs'
  let (vs, bs, hs', f) = partitionHyps vm hs 0
  let dv' = S.map (\(v1, v2) -> orientPair (vm v1, vm v2)) dv
  (bs1, bs2, hs2) <- processArgs vm dv' vs bs hs'
  let rm = I.elems (f 0 (length vs) (length vs + length bs))
  return $ SplitFrame bs1 bs2 hs2 pa rm vm
  where

  filterPos :: (a -> Bool) -> [a] -> ([a], [Int])
  filterPos f = go 0 where
    go _ [] = ([], [])
    go n (a:as) | f a = let (as', ns) = go (n+1) as in (a:as', n:ns)
    go n (_:as) = go (n+1) as

  invertB :: Maybe [Int] -> [(VarStatus, Label)] -> Q.Seq (VarStatus, Label)
  invertB Nothing = Q.fromList
  invertB (Just bs') = go 0 Q.empty bs' where
    go _ m [] [] = m
    go n m (b:bs) (a:as) | b == n = go (n+1) (m Q.|> a) bs as
    go n m (b:bs) (a:as) | fst a == VSBound =
      let f a' = if fst a' == VSBound then a' else a in
      go n (Q.adjust f b m) bs as
    go n m (_:bs) (_:as) = go n m bs as
    go _ _ _ _ = error "incorrect number of args"

  mkVarmap :: Maybe [Int] -> [Label] -> Q.Seq (VarStatus, Label) -> Label -> Label
  mkVarmap Nothing _ _ = id
  mkVarmap (Just bs) vs q =
    let m = M.fromList (zipWith (\i old -> (old, snd (Q.index q i))) bs vs) in
    \v -> M.findWithDefault v v m

  partitionHyps :: (Label -> Label) -> [(VarStatus, Label)] -> Int ->
    ([(Label, Sort)], [(Bool, Label, Sort)], [(Label, MMExpr)],
     Int -> Int -> Int -> I.IntMap Int)
  partitionHyps vm = partitionHyps' where
    partitionHyps' [] _ = ([], [], [], \_ _ _ -> I.empty)
    partitionHyps' ((b, l) : ls) li | vm l == l =
      let (vs, bs, hs', f) = partitionHyps' ls (li+1) in
      case (b, snd $ getStmt db l) of
        (VSBound, Hyp (VHyp s _)) -> ((l, s) : vs, bs, hs',
          \vi bi hi -> I.insert vi li (f (vi+1) bi hi))
        (vst, Hyp (VHyp s _)) -> (vs, (vst == VSFree, l, s) : bs, hs',
          \vi bi hi -> I.insert bi li (f vi (bi+1) hi))
        (_, Hyp (EHyp _ e)) -> (vs, bs, (l, e) : hs',
          \vi bi hi -> I.insert hi li (f vi bi (hi+1)))
        _ -> error "should not happen"
    partitionHyps' (_ : ls) li = partitionHyps' ls (li+1)

  processArgs :: (Label -> Label) -> DVs ->
    [(Label, Sort)] -> [(Bool, Label, Sort)] -> [(Label, MMExpr)] ->
    TransM ([A.Binder], [VBinder], [VExpr])
  processArgs vm dv' vs bs hs' = processBound vs where
    processBound :: [(Label, Sort)] -> TransM ([A.Binder], [VBinder], [VExpr])
    processBound [] = processReg bs
    processBound ((v, s) : vs') = do
      modify $ \t -> t {tIxLookup = ilInsertVar v (tIxLookup t)}
      (bs1, bs2, hs'') <- processBound vs'
      t <- get
      let v' = tNameMap t M.! v
      let s' = tNameMap t M.! s
      let s2 = fromJust $ ilSort (tIxLookup t) s
      return (A.Binder (A.LBound v') (A.TType $ DepType s' []) : bs1,
        VBound s2 : bs2, hs'')

    processReg :: [(Bool, Label, Sort)] -> TransM ([A.Binder], [VBinder], [VExpr])
    processReg [] = do (hs1, hs2) <- processHyps hs'; return (hs1, [], hs2)
    processReg ((fr, v, s) : bs') = do
      modify $ \t -> t {tIxLookup = ilInsertVar v (tIxLookup t)}
      (bs1, bs2, hs2) <- processReg bs'
      t <- get
      let v' = tNameMap t M.! v
      let s' = tNameMap t M.! s
      let s2 = fromJust $ ilSort (tIxLookup t) s
      let f (v2, _) = if memDVs dv' v v2 then Nothing else
            Just (tNameMap t M.! v2, fromJust $ ilVar (tIxLookup t) v2)
          (vs1, vs2) = unzip $ if fr then [] else mapMaybe f vs
      return (A.Binder (A.LReg v') (A.TType $ DepType s' vs1) : bs1,
        VReg s2 vs2 : bs2, hs2)

    processHyps :: [(Label, MMExpr)] -> TransM ([A.Binder], [VExpr])
    processHyps [] = return ([], [])
    processHyps ((l, e) : ls) = do
      modify $ \t -> t {tIxLookup = ilInsertVar l (tIxLookup t)}
      (hs1, hs2) <- processHyps ls
      (e1, e2) <- trExpr vm e
      i <- trName l (mangle l)
      return (A.Binder (A.LReg i) (A.TFormula $ exprToFmla e1) : hs1, e2 : hs2)

trNameF :: (TransState -> Maybe Ident) -> (Ident -> TransState -> TransState) -> Ident -> TransM Ident
trNameF lup set name = get >>= \m -> case lup m of
  Just s -> return s
  Nothing -> alloc (tUsedNames m) (name : ((\n -> name <> T.pack (show n)) <$> [(1::Int)..]))
  where
  alloc :: S.Set Ident -> [Ident] -> TransM Ident
  alloc _ [] = undefined
  alloc used (n : ns) | S.member n used = alloc used ns
  alloc _ (n : _) = do
    modify $ \m -> set n $ m {tUsedNames = S.insert n (tUsedNames m)}
    return n

trName :: Label -> Ident -> TransM Ident
trName lab = trNameF
  (\t -> tNameMap t M.!? lab)
  (\n t -> t {tNameMap = M.insert lab n (tNameMap t)})

trBName :: Label -> [Int] -> Ident -> TransM Ident
trBName lab bu = trNameF
  (\t -> tBNameMap t M.!? (lab, bu))
  (\n t -> t {tBNameMap = M.insert (lab, bu) n (tBNameMap t)})

trExpr :: (Label -> Label) -> MMExpr -> TransM (SExpr, VExpr)
trExpr vm = \e -> gets $ \t -> trExpr' (tNameMap t) (tBuilders t) (tIxLookup t) e where

  trExpr' :: M.Map Label Ident -> M.Map Label Builder -> IxLookup -> MMExpr -> (SExpr, VExpr)
  trExpr' names bds lup = go where
    go (SVar v) = let v' = vm v in
      (SVar (names M.! v'), VVar (fromJust $ ilVar lup v'))
    go (App t es) =
      let (es1, es2) = unzip (go <$> reorder (fst $ fromJust $ bExpr (bds M.! t)) es) in
      (App (names M.! t) es1, VApp (fromJust $ ilTerm lup t) es2)

exprToFmla :: SExpr -> A.Formula
exprToFmla e = A.Formula $ T.pack $ ' ' : showsPrec 0 e " "

identCh1 :: Char -> Bool
identCh1 c = 'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' || c == '_'

identCh :: Char -> Bool
identCh c = '0' <= c && c <= '9' || identCh1 c

identStr :: T.Text -> Bool
identStr "_" = False
identStr s = case T.uncons s of
  Nothing -> False
  Just (c, s') -> identCh1 c && T.all identCh s'

mangle :: T.Text -> Ident
mangle s = case T.uncons s of
  Nothing -> "null"
  Just (c, s') ->
    if identCh1 c then T.cons c (T.map mangle1 s')
    else T.cons '_' (T.map mangle1 s) where
    mangle1 c' = if identCh c' then c' else '_'

data HeapEl = HeapEl HeapID | HBuild (Int, [ProofTree] -> ProofTree)

ppHeapEl :: IDPrinter a => a -> HeapEl -> String
ppHeapEl a (HeapEl n) = ppVar a n
ppHeapEl a (HBuild (_, f)) = case f [] of
  VTerm n _ -> ppTerm a n
  VThm n _ -> ppThm a n
  _ -> undefined

instance Show HeapEl where show = ppHeapEl ()

trProof :: (Label -> Label) -> Int -> TransState ->
  ([Label], Proof) -> ([SortID], ProofTree)
trProof vm nhs t (ds, pr) =
  let (pr', heap) = unsave pr in
  (fromJust . ilSort lup <$> ds,
    evalState (trProof' pr') (nhs + length ds, Right <$> heap)) where
  lup = tIxLookup t

  trProof' :: Proof -> State (Int, Q.Seq (Either VarID Proof)) ProofTree
  trProof' (PHyp v _) = return $ Load $ fromJust $ ilVar lup (vm v)
  trProof' (PDummy n) = return $ Load $ VarID (nhs + n)
  trProof' (PBackref n) = do
    (_, heap) <- get
    case Q.index heap n of
      Left v -> return $ Load v
      Right p -> do
        p' <- trProof' p
        state $ \(i, heap') -> (Save p', (i+1, Q.update n (Left (VarID i)) heap'))
  trProof' PSorry = return Sorry
  trProof' (PSave _) = error "impossible, proof was unsaved"
  trProof' (PTerm st ps) = bProof (tBuilders t M.! st) <$> mapM trProof' ps
  trProof' (PThm st ps) = bProof (tBuilders t M.! st) <$> mapM trProof' ps

trSyntaxProof :: VExpr -> ([VExpr] -> VExpr, [ProofTree] -> ProofTree)
trSyntaxProof = \e -> (substVExpr e, substProof e) where

  substVExpr :: VExpr -> [VExpr] -> VExpr
  substVExpr e es = go e where
    go (VVar (VarID n)) = es !! n
    go (VApp t es') = VApp t (go <$> es')

  substProof :: VExpr -> [ProofTree] -> ProofTree
  substProof e es = go e where
    go (VVar (VarID n)) = es !! n
    go (VApp t ps) = VTerm t (go <$> ps)

findDefinitions :: MMDatabase -> M.Map Label Label
findDefinitions db = M.foldlWithKey' go M.empty (mStmts db) where
  go m x (_, Thm _ (_, App eq [App t _, _]) Nothing)
    | M.member eq (snd $ mEqual $ mMeta db) = M.insert t x m
  go m _ _ = m

trDefinition :: Int -> Label -> TransM [(Maybe A.Stmt, ProofCmd)]
trDefinition _ _ = return [] -- TODO
