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

data Builder = Builder {
  bReord :: [Int],
  bExpr :: Maybe ([VExpr] -> VExpr),
  bProof :: [ProofTree] -> ProofTree }

data TransState = TransState {
  tNameMap :: M.Map Label Ident,
  tUsedNames :: S.Set Ident,
  tBuilders :: M.Map Label Builder,
  tIxLookup :: IxLookup }

mkTransState :: TransState
mkTransState = TransState M.empty S.empty M.empty mkIxLookup

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

trDecl :: IDPrinter a => a -> Decl -> TransM (Maybe (A.Stmt, ProofCmd))
trDecl a d = ask >>= \(db, _) -> case d of
  Sort s -> case mSorts db M.! s of
    (Nothing, sd) -> do
      i <- trName s (mangle s)
      modify $ \m -> m {tIxLookup = ilInsertSort s (tIxLookup m)}
      return $ Just (A.Sort i sd, StepSort i)
    _ -> return Nothing
  Stmt st -> case mStmts db M.! st of
    Hyp (VHyp c v) ->
      trName st (if identStr v then v else mangle st) >> return Nothing
    Hyp (EHyp _ _) -> return Nothing
    Term fr s _ Nothing -> do
      (bs1, _, _, rm) <- splitFrame fr
      i <- trName st (mangle st)
      modify $ \m ->
        let {lup = tIxLookup m; n = TermID (fst (pTermIx lup))} in
        m {
          tBuilders = M.insert st
            (Builder rm (Just (VApp n)) (VTerm n))
            (tBuilders m),
          tIxLookup = ilInsertTerm st $ ilResetVars lup }
      return $ Just (A.Term i bs1 (DepType s []), StepTerm i)
    Term fr s e (Just _) -> do
      (_, _, _, rm) <- splitFrame fr
      (_, e2) <- trExpr e
      let (be, bd) = trSyntaxProof e2
      modify $ \t -> t {
        tBuilders = M.insert st (Builder rm (Just be) bd) (tBuilders t),
        tIxLookup = ilResetVars $ tIxLookup t }
      return Nothing
    Thm fr s e p -> do
      (bs1, bs2, hs2, rm) <- splitFrame fr
      (e1, e2) <- trExpr e
      i <- trName st (mangle st)
      ret <- case p of
        Nothing -> return (A.Axiom i bs1 (exprToFmla e1), StepAxiom i)
        Just p -> do
          t <- get
          let (ds, pr) = trProof fr t p
          return (A.Theorem i bs1 (exprToFmla e1),
            ProofThm (Just i) bs2 hs2 e2 [] ds pr True)
      modify $ \m ->
        let {lup = tIxLookup m; n = ThmID (fst (pThmIx lup))} in
        m {
          tBuilders = M.insert st (Builder rm Nothing (VThm n)) (tBuilders m),
          tIxLookup = ilInsertThm st $ ilResetVars lup }
      return $ Just ret

splitFrame :: Frame -> TransM ([A.Binder], [VBinder], [VExpr], [Int])
splitFrame (hs, ds) = do (db, _) <- ask; splitFrame' hs ds db
splitFrame' hs ds db = do
  let (vs, bs, hs', f) = partitionHyps hs 0
  (bs1, bs2, hs2) <- processArgs vs bs hs'
  return (bs1, bs2, hs2, I.elems (f 0 (length vs) (length vs + length bs)))
  where

  partitionHyps :: [(Bool, Label)] -> Int -> ([(Var, Label, Sort)],
    [(Var, Label, Sort)], [(Label, MMExpr)], Int -> Int -> Int -> I.IntMap Int)
  partitionHyps [] _ = ([], [], [], \_ _ _ -> I.empty)
  partitionHyps ((b, l) : ls) li = case mStmts db M.! l of
    Hyp (VHyp s v) ->
      let (vs, bs, hs', f) = partitionHyps ls (li+1) in
      if b then ((v, l, s) : vs, bs, hs',
        \vi bi hi -> I.insert vi li (f (vi+1) bi hi))
      else (vs, (v, l, s) : bs, hs',
        \vi bi hi -> I.insert bi li (f vi (bi+1) hi))
    Hyp (EHyp _ e) ->
      let (vs, bs, hs, f) = partitionHyps ls (li+1) in
      (vs, bs, (l, e) : hs,
        \vi bi hi -> I.insert hi li (f vi bi (hi+1)))

  processArgs :: [(Var, Label, Sort)] -> [(Var, Label, Sort)] -> [(Label, MMExpr)] ->
    TransM ([A.Binder], [VBinder], [VExpr])
  processArgs vs bs hs = processBound vs where
    processBound :: [(Var, Label, Sort)] -> TransM ([A.Binder], [VBinder], [VExpr])
    processBound [] = processReg bs
    processBound ((_, l, s) : vs) = do
      modify $ \t -> t {tIxLookup = ilInsertVar l (tIxLookup t)}
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
      modify $ \t -> t {tIxLookup = ilInsertVar l (tIxLookup t)}
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

    processHyps :: [(Label, MMExpr)] -> TransM ([A.Binder], [VExpr])
    processHyps [] = return ([], [])
    processHyps ((l, e) : ls) = do
      modify $ \t -> t {tIxLookup = ilInsertVar l (tIxLookup t)}
      (hs1, hs2) <- processHyps ls
      (e1, e2) <- trExpr e
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
trExpr = \e -> (\t -> trExpr' (tNameMap t) (tBuilders t) (tIxLookup t) e) <$> get where

  trExpr' :: M.Map Label Ident -> M.Map Label Builder -> IxLookup -> MMExpr -> (SExpr, VExpr)
  trExpr' names bds lup = go where
    go (SVar v) = (SVar (names M.! v), VVar (fromJust $ ilVar lup v))
    go (App t es) =
      let (es1, es2) = unzip (go . (es !!) <$> bReord (bds M.! t)) in
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
trProof (hs, _) t (ds, pr) =
  let (pr', heap) = unsave pr in
  (fromJust . ilSort lup <$> ds,
    evalState (trProof' pr') (nhs + nds, Right <$> heap)) where

  lup = tIxLookup t
  nhs = length hs
  nds = length ds

  trProof' :: Proof -> State (Int, Q.Seq (Either VarID Proof)) ProofTree
  trProof' (PHyp v _) = return $ Load $ fromJust $ ilVar lup v
  trProof' (PDummy n) = return $ Load $ VarID (nhs + n)
  trProof' (PBackref n) = do
    (_, heap) <- get
    case Q.index heap n of
      Left v -> return $ Load v
      Right p -> do
        p' <- trProof' p
        state $ \(i, heap) -> (Save p', (i+1, Q.update n (Left (VarID i)) heap))
  trProof' PSorry = return Sorry
  trProof' (PSave p) = error "impossible, proof was unsaved"
  trProof' (PTerm st ps) =
    let Builder rm _ pf = tBuilders t M.! st in
    pf <$> mapM (trProof' . (ps !!)) rm
  trProof' (PThm st ps) =
    let Builder rm _ pf = tBuilders t M.! st in
    pf <$> mapM (trProof' . (ps !!)) rm

trSyntaxProof :: VExpr -> ([VExpr] -> VExpr, [ProofTree] -> ProofTree)
trSyntaxProof e = (substExpr e, substProof e) where

  substExpr :: VExpr -> [VExpr] -> VExpr
  substExpr e es = go e where
    go (VVar (VarID n)) = es !! n
    go (VApp t es') = VApp t (go <$> es')

  substProof :: VExpr -> [ProofTree] -> ProofTree
  substProof e es = go e where
    go (VVar (VarID n)) = es !! n
    go (VApp t ps) = VTerm t (go <$> ps)
