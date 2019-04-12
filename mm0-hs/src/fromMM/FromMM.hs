module FromMM where

import System.IO
import System.Exit
import System.Environment
import Control.Monad.RWS.Strict hiding (liftIO)
import Control.Monad.Except hiding (liftIO)
import Data.Foldable
import Data.Maybe
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString.Char8 as C
import qualified Data.Map.Strict as M
import qualified Data.IntMap as I
import qualified Data.Set as S
import Util
import MMTypes
import MMParser
import Environment (Ident, DepType(..), SortData(..), SExpr(..))
import ProofTypes
import qualified AST as A

fromMM :: [String] -> IO ()
fromMM [] = die "from-mm: no .mm file specified"
fromMM (mm : rest) = do
  db <- withFile mm ReadMode $ \h ->
    B.hGetContents h >>= liftIO . parseMM
  (ast, pfs) <- liftIO $ makeAST db
  (mm0, mmu) <- case rest of
    [] -> return (\k -> k stdout, Nothing)
    "-o" : mm0 : [] -> return (withFile mm0 WriteMode, Nothing)
    "-o" : mm0 : mmu : _ -> return (withFile mm0 WriteMode, Just mmu)
    _ -> die "from-mm: too many arguments"
  mm0 $ \h -> do
    hSetNewlineMode h (NewlineMode LF LF)
    mapM_ (\d -> hPutStrLn h $ shows d "\n") ast
  mapM_ (\mmu -> withFile mmu WriteMode $ \h -> do
    hSetNewlineMode h (NewlineMode LF LF)
    mapM_ (\d -> hPutStrLn h $ shows d "\n") pfs) mmu

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
  tIxLookup :: IxLookup }

type TransM = RWST MMDatabase (Endo A.AST, Endo Proofs) TransState (Either String)

runTransM :: TransM a -> MMDatabase -> Either String (a, (A.AST, Proofs))
runTransM m db = do
  (a, (Endo f, Endo g)) <- evalRWST m db
    (TransState M.empty M.empty M.empty M.empty S.empty mkIxLookup)
  return (a, (A.Notation (A.Delimiter $ A.Const $ C.pack " ( ) ") : f [], g []))

makeAST :: MMDatabase -> Either String (A.AST, Proofs)
makeAST db = snd <$> runTransM (mapM_ trDecl (mDecls db)) db

emit :: A.Stmt -> ProofCmd -> TransM ()
emit d p = tell (Endo (d :), Endo (p :))

fromJust' :: String -> Maybe a -> a
fromJust' _ (Just a) = a
fromJust' s Nothing = error $ "fromJust: " ++ s

-- (<!>) :: (HasCallStack, Ord k, Show k, Show v) => M.Map k v -> k -> v
-- (<!>) m k = case m M.!? k of
--   Nothing -> error $ show m ++ " ! " ++ show k
--   Just v -> v

type ParseResult = [(([MMExpr] -> [MMExpr]) -> MMExpr, [Sym])]
parseFmla :: Fmla -> TransM MMExpr
parseFmla = \case
  Const s : f -> do
    t <- get
    db <- ask
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

trDecl :: Decl -> TransM ()
trDecl d = ask >>= \db -> case d of
  Sort s -> case mSorts db M.! s of
    (Nothing, sd) -> do
      i <- trName s (mangle s)
      emit (A.Sort i sd) (StepSort i)
      modify $ \m -> m {tIxLookup = ilInsertSort s (tIxLookup m)}
    _ -> return ()
  Stmt st -> case mStmts db M.! st of
    Hyp (VHyp c v) -> do
      trName st (if identStr v then v else mangle st)
      modify $ \m -> m {tVMap = M.insert v (c, st) (tVMap m)}
    Hyp (EHyp f) -> do
      e <- parseFmla f
      modify $ \m -> m {tParsedHyps = M.insert st e (tParsedHyps m)}
    Thm fr f@(Const s : _) [] | isNothing (fst (mSorts db M.! s)) -> do
      (bs1, _, _, reord) <- splitFrame fr
      i <- trName st (mangle st)
      let g = App st . reorderMap reord f
      modify $ \m -> m {
        tParser = ptInsert (tVMap m) g f (tParser m),
        tIxLookup = ilInsertTerm st $ ilResetVars $ tIxLookup m }
      emit (A.Term i bs1 (DepType s [])) (StepTerm i)
    Thm fr f@(Const s : _) p -> do
      (bs1, bs2, hs2, _) <- splitFrame fr
      (e1, e2) <- parseFmla f >>= trExpr
      i <- trName st (mangle st)
      case p of
        [] -> emit (A.Axiom i bs1 (exprToFmla e1)) (StepAxiom i)
        _ -> do
          (ds, pr) <- trProof p
          emit (A.Theorem i bs1 (exprToFmla e1))
            (ProofThm (Just i) bs2 hs2 e2 [] ds pr True)
      modify $ \m -> m {tIxLookup = ilInsertThm st $ ilResetVars $ tIxLookup m}
    Thm _ _ _ -> throwError "bad theorem statement"

splitFrame :: Frame -> TransM ([A.Binder], [VBinder], [VExpr], M.Map Var Int)
splitFrame (hs, ds) = do db <- ask; splitFrame' hs ds db
splitFrame' hs ds db = do
  (vs, bs, hs') <- partitionHyps hs
  (bs1, bs2, hs2) <- processArgs vs bs hs'
  return (bs1, bs2, hs2, buildReorder (vs ++ bs) 0 M.empty)
  where

  partitionHyps :: [Label] -> TransM ([(Var, Label, Sort)], [(Var, Label, Sort)], [Label])
  partitionHyps (l : ls) = case mStmts db M.! l of
    Hyp (VHyp s v) -> do
      (vs, bs, hs') <- partitionHyps ls
      if sPure (snd (mSorts db M.! s)) then
        return ((v, l, s) : vs, bs, hs')
      else return (vs, (v, l, s) : bs, hs')
    Hyp (EHyp _) -> (\(vs, bs, hs) -> (vs, bs, l : hs)) <$> partitionHyps ls
  partitionHyps [] = return ([], [], [])

  processArgs :: [(Var, Label, Sort)] -> [(Var, Label, Sort)] -> [Label] ->
    TransM ([A.Binder], [VBinder], [VExpr])
  processArgs vs bs hs = processBound vs where
    processBound :: [(Var, Label, Sort)] -> TransM ([A.Binder], [VBinder], [VExpr])
    processBound [] = processReg bs
    processBound ((_, l, s) : vs) = do
      modify $ \g -> g {tIxLookup = ilInsertVar l (tIxLookup g)}
      (bs1, bs2, hs') <- processBound vs
      t <- get
      let v' = fromJust' "a" $ tNameMap t M.!? l
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
      let v' = fromJust' "b" $ tNameMap t M.!? l
      let s' = tNameMap t M.! s
      let s2 = fromJust $ ilSort (tIxLookup t) s
      let f (v2, l2, _) = if memDVs ds v v2 then
              Just (tNameMap t M.! l2, fromJust $ ilVar (tIxLookup t) l)
            else Nothing
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
  go (SVar v) = (SVar (names M.! v), VVar (fromJust' (show (pVarIx lup, v)) $ ilVar lup v))
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

trProof :: Proof -> TransM ([SortID], [LocalCmd])
trProof p = return ([], [Sorry])
