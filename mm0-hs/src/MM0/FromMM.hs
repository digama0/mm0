module MM0.FromMM (fromMM, showBundled) where

import System.IO
import System.Exit
import Control.Monad.State
import Control.Monad.RWS.Strict
import Data.Foldable
import Data.Maybe
import Data.Either
import Data.List
import Data.Default
import qualified Data.ByteString.Lazy as B
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Q
import qualified Data.IntMap as I
import qualified Data.Set as S
import qualified Data.Text as T
import MM0.Util
import MM0.FromMM.Types as T
import MM0.FromMM.Parser
import MM0.FromMM.Emancipate
import MM0.FromMM.Closure
import MM0.FromMM.FindBundled
import MM0.Kernel.Environment (Ident, DepType(..), SExpr(..), PBinder(..),
  VarName, TermName, ThmName, Comment)
import MM0.Kernel.Types as K
import MM0.Compiler.Export (exportKP)
import qualified MM0.FrontEnd.AST as A

type KStmt = (Comment, K.Stmt)

showsK :: KStmt -> ShowS
showsK (c, s) = A.showsComment c . shows s

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
  case rest' of
    [] -> printAST db' dbf (\a -> putStr (shows a "\n\n")) (\_ -> return ())
    "-o" : mm0 : [] ->
      write mm0 $ \h -> printAST db' dbf
        (\a -> hPutStr h (shows a "\n\n")) (\_ -> return ())
    "-o" : mm0 : mmo : _ ->
      if isSuffixOf "mmb" mmo then
        write mm0 $ \hmm0 -> exportKP False mmo $ \f ->
          printAST db' dbf (\a -> hPutStr hmm0 (shows a "\n\n")) (f . snd)
      else write mm0 $ \hmm0 -> write mmo $ \hmmu ->
        printAST db' dbf
          (\a -> hPutStr hmm0 (shows a "\n\n"))
          (\a -> hPutStr hmmu (showsK a "\n\n"))
    _ -> die "from-mm: too many arguments"

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
  bExpr :: ([Int], [SExpr] -> SExpr),
  bProof :: [Either SExpr Proof] -> Either SExpr Proof }

data TransState = TransState {
  tNameMap :: M.Map Label Ident,
  tBNameMap :: M.Map (Label, [Int]) Ident,
  tUsedNames :: S.Set Ident,
  tBuilders :: M.Map Label Builder }

instance Default TransState where
  def = TransState def def def def

type TransM = RWST (MMDatabase, DBInfo)
  (Endo [String]) TransState (Either String)

runTransM :: TransM a -> MMDatabase -> DBFilter -> TransState -> Either String (a, TransState, [String])
runTransM m db dbf st = do
  let i = DBInfo dbf (findBundled db) (findDefinitions db)
  (os, st', Endo w) <- runRWST m (db, i) st
  return (os, st', w [])

_makeAST :: MMDatabase -> DBFilter -> Either String (A.AST, [KStmt])
_makeAST db dbf = trDecls (mDecls db)
  (A.Notation (A.Delimiter (A.Const $ T.pack " ( ") (Just $ A.Const $ T.pack " ) ")) :) id def where
  trDecls :: Q.Seq Decl -> (A.AST -> A.AST) -> ([KStmt] -> [KStmt]) ->
    TransState -> Either String (A.AST, [KStmt])
  trDecls Q.Empty f g _ = return (f [], g [])
  trDecls (d Q.:<| ds) f g st = do
    (os, st', _) <- runTransM (trDecl d) db dbf st
    let (ds', ps) = unzip os
    trDecls ds (f . (catMaybes ds' ++)) (g . (ps ++)) st'

printAST :: MMDatabase -> DBFilter -> (A.Stmt -> IO ()) -> (KStmt -> IO ()) -> IO ()
printAST db dbf mm0 mmu = do
  mm0 (A.Notation $ A.Delimiter (A.Const $ T.pack " ( ") (Just $ A.Const $ T.pack " ) "))
  trDecls (mDecls db) def
  where
  trDecls :: Q.Seq Decl -> TransState -> IO ()
  trDecls Q.Empty _ = return ()
  trDecls (d Q.:<| ds) st = do
    (os, st', w) <- liftIO' (runTransM (trDecl d) db dbf st)
    forM_ os $ \(a, pf) -> forM_ a mm0 >> mmu pf
    mapM_ (hPutStrLn stderr) w
    trDecls ds st'

-- fromJust' :: String -> Maybe a -> a
-- fromJust' _ (Just a) = a
-- fromJust' s Nothing = error $ "fromJust: " ++ s

-- (<!>) :: (HasCallStack, Ord k, Show k) => M.Map k v -> k -> v
-- (<!>) m k = case m M.!? k of
--   Nothing -> error $ show (M.keys m) ++ " ! " ++ show k
--   Just v -> v

reorder :: [Int] -> [a] -> [a]
reorder ns l = (l !!) <$> ns

trDecl :: Decl -> TransM [(Maybe A.Stmt, KStmt)]
trDecl d = get >>= \t -> ask >>= \(db, i) -> case d of
  Sort s -> if sortMember i s then
    case mSorts db M.! s of
      (Nothing, sd) -> do
        st' <- trName s (mangle s)
        return [(Just $ A.Sort Nothing st' sd, (Nothing, StmtSort st' sd))]
      _ -> return []
    else return []
  Stmt st -> if stmtMember i st && M.notMember st (tNameMap t) then
    case getStmt db st of
      (_, Hyp (VHyp _ v)) ->
        trName st (if identStr v then v else mangle st) >> return []
      (_, Hyp (EHyp _ _)) -> return []
      (ix, Term c fr (s, _) Nothing) -> trDefinition ix st >>= \case
        [] -> do
          splitFrame Nothing fr $ \(SplitFrame bs1 bs2 _ _ rm _) -> do
            st' <- trName st (mangle st)
            modify $ \m -> m {
              tBuilders = M.insert st
                (mkAppBuilder rm (App st'))
                (tBuilders m) }
            return [(
              Just $ A.Term c st' bs1 (DepType s []),
              (c, StmtTerm st' bs2 (DepType s [])))]
        e -> return e
      (_, Term _ fr (_, e) (Just _)) -> splitFrame Nothing fr $ \sf -> do
        let rm = sfReord sf
        e2 <- trExpr id e
        modify $ \t' -> t' {
          tBuilders = M.insert st
            (mkAppBuilder rm (trSyntaxProof fr t' e2))
            (tBuilders t') }
        return []
      (_, Thm c fr e p) -> do
        let mst = mangle st
        let pub = stmtPublic i st
        n <- trName st mst
        (out, pa, rm) <- trThmB c Nothing pub fr e p n
        (out2, ns) <- unzip <$> mapM (\bu -> do
          n' <- trBName st bu (mst <> "_b")
          (out', _, rm') <- trThmB c (Just bu) pub fr e p n'
          return (out', (bu, (n', rm'))))
          (maybe [] M.keys (dbiBundles i M.!? st))
        modify $ \t' -> t' {tBuilders = M.insert st (mkThmBuilder pa rm n ns) (tBuilders t')}
        return (out : out2)
      (_, Alias _) -> return []
    else return []

trThmB :: Comment -> Maybe [Int] -> Bool -> Frame -> (Const, MMExpr) ->
  Maybe ([(Label, Label)], MMProof) -> ThmName ->
  TransM ((Maybe A.Stmt, KStmt), [Int], [Int])
trThmB c bu pub fr (_, e) p i =
  splitFrame bu fr $ \(SplitFrame bs1 bs2 hs2 pa rm vm) -> do
    e1 <- trExpr vm e
    ret <- case p of
      Nothing -> return (
        Just $ A.Axiom c i bs1 (exprToFmla e1),
        (c, StmtAxiom i bs2 (snd <$> hs2) e1))
      Just p' -> do
        t <- get
        let (ds, pr) = trProof vm t p'
        return (
          if pub then Just $ A.Theorem c i bs1 (exprToFmla e1) else Nothing,
          (c, StmtThm i bs2 hs2 e1 ds pr pub))
    return (ret, pa, rm)

mkAppBuilder :: [Int] -> ([SExpr] -> SExpr) -> Builder
mkAppBuilder rm f = Builder (rm, f)
  (Left . f . fmap (fromLeft undefined) . reorder rm)

mkThmBuilder :: [Int] -> [Int] -> ThmName -> [([Int], (ThmName, [Int]))] -> Builder
mkThmBuilder _ rm n [] = Builder undefined $
  Right . uncurry (K.PThm n) . partitionEithers . reorder rm
mkThmBuilder pa rm n ns = let m = M.fromList ns in
  Builder undefined $ \ps -> Right $
    let vs = (\(Left (SVar v)) -> v) <$> reorder pa ps in
    if allUnique vs then
      uncurry (K.PThm n) $ partitionEithers $ reorder rm ps
    else
      let {bu = bundle vs; (t, rm') = m M.! bu} in
      uncurry (K.PThm t) $ partitionEithers $ reorder rm' ps

data SplitFrame = SplitFrame {
  _sfBound :: [A.Binder],
  _sfPBound :: [PBinder],
  _sfHyps :: [(VarName, SExpr)],
  _sfPureArgs :: [Int],
  sfReord :: [Int],
  _sfVarmap :: Label -> Label }

splitFrame :: Maybe [Int] -> Frame -> (SplitFrame -> TransM a) -> TransM a
splitFrame bu (hs, dv) k = ask >>= splitFrame' bu hs dv . fst >>= k
splitFrame' :: Maybe [Int] -> [(VarStatus, Label)] -> DVs ->
  MMDatabase -> TransM SplitFrame
splitFrame' bu hs dv db = do
  let (vs1, pa) = filterPos (vsPure . fst) hs
  let vs' = invertB bu vs1
  let vm = mkVarmap bu (snd <$> vs1) vs'
  let (vs, bs, hs', f) = partitionHyps vm hs 0
  let dv' = S.map (\(v1, v2) -> orientPair (vm v1, vm v2)) dv
  (bs1, bs2, hs2) <- processArgs vm dv' vs bs hs'
  let rm = I.elems $ f 0 (length vs) (length vs + length bs)
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
    TransM ([A.Binder], [PBinder], [(VarName, SExpr)])
  processArgs vm dv' vs bs hs' = processBound vs where
    processBound :: [(Label, Sort)] -> TransM ([A.Binder], [PBinder], [(VarName, SExpr)])
    processBound [] = processReg bs
    processBound ((v, s) : vs') = do
      (bs1, bs2, hs'') <- processBound vs'
      t <- get
      let v' = tNameMap t M.! v
      let s' = tNameMap t M.! s
      return (A.Binder (A.LBound v') (A.TType $ DepType s' []) : bs1,
        PBound v' s' : bs2, hs'')

    processReg :: [(Bool, Label, Sort)] -> TransM ([A.Binder], [PBinder], [(VarName, SExpr)])
    processReg [] = do (hs1, hs2) <- processHyps hs'; return (hs1, [], hs2)
    processReg ((fr, v, s) : bs') = do
      (bs1, bs2, hs2) <- processReg bs'
      t <- get
      let v' = tNameMap t M.! v
      let s' = tNameMap t M.! s
      let f (v2, _) = if memDVs dv' v v2 then Nothing else Just (tNameMap t M.! v2)
      let vs1 = if fr then [] else mapMaybe f vs
      return (A.Binder (A.LReg v') (A.TType $ DepType s' vs1) : bs1,
        PReg v' (DepType s' vs1) : bs2, hs2)

    processHyps :: [(Label, MMExpr)] -> TransM ([A.Binder], [(VarName, SExpr)])
    processHyps [] = return ([], [])
    processHyps ((l, e) : ls) = do
      (hs1, hs2) <- processHyps ls
      e1 <- trExpr vm e
      i <- trName l (mangle l)
      return (A.Binder (A.LReg i) (A.TFormula $ exprToFmla e1) : hs1, (i, e1) : hs2)

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

trExpr :: (Label -> Label) -> MMExpr -> TransM SExpr
trExpr vm = \e -> gets $ \t -> trExpr' (tNameMap t) (tBuilders t) e where

  trExpr' :: M.Map Label Ident -> M.Map Label Builder -> MMExpr -> SExpr
  trExpr' names bds = go where
    go (SVar v) = let v' = vm v in SVar (names M.! v')
    go (App t es) = App (names M.! t) $
      go <$> reorder (fst $ bExpr (bds M.! t)) es

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

trProof :: (Label -> Label) -> TransState ->
  ([(Label, Label)], MMProof) -> ([(VarName, Sort)], Proof)
trProof vm t (ds, pr) = (
  (\(d, s) -> (tNameMap t M.! d, tNameMap t M.! s)) <$> ds,
  fromRight undefined $ evalState (trProof' pr) def)
  where

  toHeapEl :: (VarStatus, Label) -> Either SExpr Proof
  toHeapEl (VSHyp, l) = Right $ K.PHyp $ tNameMap t M.! l
  toHeapEl (_, l) = Left $ SVar $ tNameMap t M.! vm l

  trProof' :: MMProof -> State (Q.Seq (Either SExpr Proof)) (Either SExpr Proof)
  trProof' (T.PHyp s v _) = return $ toHeapEl (s, v)
  trProof' (PDummy v) = return $ Left $ SVar (tNameMap t M.! v)
  trProof' (PBackref n) = gets (`Q.index` n)
  trProof' T.PSorry = return $ Right K.PSorry
  trProof' (PSave p) = do
    p' <- trProof' p
    state $ \q -> (p', q Q.|> p')
  trProof' (T.PTerm st ps) = bProof (tBuilders t M.! st) <$> mapM trProof' ps
  trProof' (T.PThm st ps) = bProof (tBuilders t M.! st) <$> mapM trProof' ps

data NExpr = NVar Int | NApp TermName [NExpr]

trSyntaxProof :: Frame -> TransState -> SExpr -> [SExpr] -> SExpr
trSyntaxProof (hs, _) t = substSExpr . toNExpr (mkMap hs 0 M.empty) where
  mkMap :: [(VarStatus, Label)] -> Int -> M.Map VarName Int -> M.Map VarName Int
  mkMap [] _ m = m
  mkMap ((_, l) : hs') n m =
    mkMap hs' (n+1) (M.insert (tNameMap t M.! l) n m)

  toNExpr :: M.Map VarName Int -> SExpr -> NExpr
  toNExpr m (SVar v) = NVar (m M.! v)
  toNExpr m (App st es') = NApp st (toNExpr m <$> es')

  substSExpr :: NExpr -> [SExpr] -> SExpr
  substSExpr e es = go e where
    go (NVar v) = es !! v
    go (NApp st es') = App st (go <$> es')

findDefinitions :: MMDatabase -> M.Map Label Label
findDefinitions db = M.foldlWithKey' go M.empty (mStmts db) where
  go m x (_, Thm _ _ (_, App eq [App t _, _]) Nothing)
    | M.member eq (snd $ mEqual $ mMeta db) = M.insert t x m
  go m _ _ = m

trDefinition :: Int -> Label -> TransM [(Maybe A.Stmt, KStmt)]
trDefinition _ _ = return [] -- TODO
