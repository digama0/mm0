module MMParser (parseMM) where

import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import Control.Monad.Trans.State
import Control.Monad.Except hiding (liftIO)
import qualified Text.ParserCombinators.ReadP as P
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString.Lazy.Char8 as C
import qualified Data.IntMap as I
import qualified Text.Read.Lex as L
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Q
import qualified Data.Set as S
import Environment (SortData(..), SExpr(..))
import MMTypes
import Util

parseMM :: B.ByteString -> Either String MMDatabase
parseMM s = snd <$> runFromMMM (process (toks s))

toks :: B.ByteString -> [String]
toks = filter (not . null) . map C.unpack .
  C.splitWith (`elem` [' ', '\n', '\t', '\r'])

data Sym = Const Const | Var Var deriving (Show)
type Fmla = [Sym]

data ParseTrie = PT {
  ptConst :: Parser,
  ptVar :: M.Map Sort ParseTrie,
  ptDone :: Maybe (Sort, [MMExpr] -> MMExpr) }
type Parser = M.Map Const ParseTrie

type Scope = [([(Label, Hyp)], [[Label]], S.Set Label)]

data MMParserState = MMParserState {
  mParser :: Parser,
  mVMap :: M.Map Var (Sort, Label),
  mSyms :: M.Map String Sym,
  mScope :: Scope,
  mDB :: MMDatabase }

type FromMMM = StateT MMParserState (Either String)

modifyDB :: (MMDatabase -> MMDatabase) -> FromMMM ()
modifyDB f = modify $ \s -> s {mDB = f (mDB s)}

withContext :: MonadError String m => String -> m a -> m a
withContext s m = catchError m (\e -> throwError ("at " ++ s ++ ": " ++ e))

runFromMMM :: FromMMM a -> Either String (a, MMDatabase)
runFromMMM m = (\(a, t) -> (a, mDB t)) <$>
  runStateT m (MMParserState M.empty M.empty M.empty [([], [], S.empty)] mkDatabase)

addConstant :: Const -> FromMMM ()
addConstant c = modify $ \s -> s {mSyms = M.insert c (Const c) (mSyms s)}

addVariable :: Var -> FromMMM ()
addVariable v = modify $ \s -> s {mSyms = M.insert v (Var v) (mSyms s)}

exprVars :: MMExpr -> S.Set Label
exprVars (SVar v) = S.singleton v
exprVars (App _ es) = foldMap exprVars es

fmlaVars :: Fmla -> S.Set Var
fmlaVars [] = S.empty
fmlaVars (Const _ : ss) = fmlaVars ss
fmlaVars (Var v : ss) = S.insert v (fmlaVars ss)

fmlaVHyps :: Fmla -> FromMMM (S.Set Label)
fmlaVHyps f = do t <- get; return (S.map (\v -> snd (mVMap t M.! v)) (fmlaVars f))

scopeAddHyp :: Label -> Hyp -> S.Set Var -> Scope -> Scope
scopeAddHyp x h vs1 ((hs, ds, vs) : s) = ((x, h):hs, ds, S.union vs1 vs) : s

scopeAddDV :: [Label] -> Scope -> Scope
scopeAddDV ds' ((hs, ds, vs) : s) = (hs, ds' : ds, vs) : s

scopeOpen :: Scope -> Scope
scopeOpen ss@((_, _, vs) : _) = ([], [], vs) : ss

scopeClose :: Scope -> Maybe Scope
scopeClose (_ : []) = Nothing
scopeClose (_ : s : ss) = Just (s : ss)

addHyp :: Label -> Hyp -> S.Set Label -> FromMMM ()
addHyp x h vs = do
  addStmt x (Hyp h)
  modify $ \t -> t {mScope = scopeAddHyp x h vs (mScope t)}

mkFrame :: Fmla -> FromMMM (Frame, M.Map Var Int)
mkFrame f = do
  t <- get
  let sc@((_, _, vs) : _) = mScope t
  vs' <- fmlaVHyps f
  return (build (mDB t) (S.union vs vs') sc ([], S.empty) (M.empty, 0))

build :: MMDatabase -> S.Set Label -> Scope ->
  Frame -> (M.Map Var Int, Int) -> (Frame, M.Map Var Int)
build db vars = go where
  go [] fr (m, _) = (fr, m)
  go ((hs, ds, _) : sc) (hs', ds') m' =
    let (hs'', m'') = insertHyps hs hs' m' in
    go sc (hs'', foldl' insertDVs ds' ds) m''

  insertHyps :: [(Label, Hyp)] -> [(Bool, String)] -> (M.Map Var Int, Int) ->
    ([(Bool, String)], (M.Map Var Int, Int))
  insertHyps [] hs' m = (hs', m)
  insertHyps ((x, EHyp _ _):hs) hs' m =
    insertHyps hs ((False, x):hs') m
  insertHyps ((x, VHyp s v):hs) hs' m =
    let (hs'', (m', n)) = insertHyps hs
          (if S.member x vars then
            (sPure (snd (mSorts db M.! s)), x) : hs' else hs') m in
    (hs'', (M.insert v n m', n+1))

  insertDVs :: DVs -> [Label] -> DVs
  insertDVs ds [] = ds
  insertDVs ds (v:vs) = let ds' = insertDVs ds vs in
    if S.member v vars then foldl' (insertDV1 v) ds' vs else ds'

  insertDV1 :: Label -> DVs -> Label -> DVs
  insertDV1 v1 ds v2 =
    if S.member v2 vars then
      S.insert (if v1 < v2 then (v1, v2) else (v2, v1)) ds
    else ds

addSort :: Sort -> Maybe Sort -> FromMMM ()
addSort x s2 = modifyDB $ \db -> db {
  mSorts = M.insert x (s2, SortData False False False False) (mSorts db),
  mDecls = mDecls db Q.|> Sort x }

addStmt :: Label -> Stmt -> FromMMM ()
addStmt x st = modifyDB $ \db -> db {
  mDecls = mDecls db Q.|> Stmt x,
  mStmts = M.insert x st (mStmts db) }

process :: [String] -> FromMMM ()
process [] = return ()
process ("$(" : "$j" : ss) = processJ (parseJ ss)
process ("$(" : ss) = readUntil "$)" ss >>= process . snd
process ("$c" : ss) = do
  (cs, ss') <- readUntil "$." ss
  mapM_ addConstant cs >> process ss'
process ("$v" : ss) = do
  (vs, ss') <- readUntil "$." ss
  mapM_ addVariable vs >> process ss'
process ("$d" : ss) = do
  (vs, ss') <- readUntil "$." ss
  t <- get
  let vs' = (\v -> snd (mVMap t M.! v)) <$> vs
  modify $ \t -> t {mScope = scopeAddDV vs' (mScope t)}
  process ss'
process ("${" : ss) = do
  modify $ \t -> t {mScope = scopeOpen (mScope t)}
  process ss
process ("$}" : ss) = do
  t <- get
  sc <- fromJustError "too many $}" (scopeClose (mScope t))
  put $ t {mScope = sc}
  process ss
process (x : "$f" : c : v : "$." : ss) = do
  modify $ \t -> t {mVMap = M.insert v (c, x) (mVMap t)}
  addHyp x (VHyp c v) S.empty
  process ss
process (x : "$e" : ss) = do
  (f, ss') <- withContext x $ readMath "$." ss
  (s, e) <- parseFmla f
  withContext x $ addHyp x (EHyp s e) (exprVars e)
  process ss'
process (x : "$a" : ss) = do
  (f, ss') <- withContext x $ readMath "$." ss
  withContext x $ do
    (fr, m) <- mkFrame f
    addThm x f fr m Nothing
  process ss'
process (x : "$p" : ss) = do
  (f, ss1) <- withContext x $ readMath "$=" ss
  (p, ss2) <- readProof ss1
  withContext x $ do
    (fr, m) <- mkFrame f
    t <- get
    pr <- lift $ trProof fr (mDB t) p
    addThm x f fr m (Just pr)
  process ss2
process (x : ss) = throwError ("wtf " ++ x ++ show (take 100 ss))

addThm :: Label -> Fmla -> Frame -> M.Map Var Int ->
  Maybe ([Label], Proof) -> FromMMM ()
addThm x f@(Const s : _) fr m p = do
  db <- mDB <$> get
  case mSorts db M.!? s of
    Nothing -> throwError ("sort '" ++ s ++ "' not declared")
    Just (Just s', _) -> do
      (_, e) <- parseFmla f
      addStmt x (Thm fr s' e p)
    Just (Nothing, _) -> do
      when (isNothing p) $
        let g = App x . reorderMap m f in
        modify $ \t -> t {
          mParser = ptInsert (mVMap t) g f (mParser t) }
      (s, e) <- parseFmla f
      addStmt x (Term fr s e p)

readUntil :: String -> [String] -> FromMMM ([String], [String])
readUntil u = go id where
  go f [] = throwError "unclosed command"
  go f ("$(" : ss) = readUntil "$)" ss >>= go f . snd
  go f (s : ss) | s == u = return (f [], ss)
  go f (s : ss) = go (f . (s:)) ss

readMath :: String -> [String] -> FromMMM (Fmla, [String])
readMath u ss = do
  (sy, ss') <- readUntil u ss
  t <- get
  f <- mapM (\s ->
    fromJustError ("unknown symbol '" ++ s ++ "'") (mSyms t M.!? s)) sy
  return (f, ss')

readProof :: [String] -> FromMMM ([String], [String])
readProof = go id where
  go f [] = throwError "unclosed $p"
  go f ("$." : ss) = return (f [], ss)
  go f (s : ss) = go (f . (s:)) ss

data Numbers =
    NNum Int Numbers
  | NSave Numbers
  | NSorry Numbers
  | NEOF
  | NError

instance Show Numbers where
  showsPrec _ (NNum n ns) r = shows n (' ' : shows ns r)
  showsPrec _ (NSave ns) r = "Z " ++ shows ns r
  showsPrec _ (NSorry ns) r = "? " ++ shows ns r
  showsPrec _ NEOF r = r
  showsPrec _ NError r = "err" ++ r

numberize :: String -> Int -> Numbers
numberize "" n = if n == 0 then NEOF else NError
numberize ('?' : s) n = if n == 0 then NSorry (numberize s 0) else NError
numberize ('Z' : s) n = if n == 0 then NSave (numberize s 0) else NError
numberize (c : s) n | 'A' <= c && c <= 'Y' =
  if c < 'U' then
    let i = ord c - ord 'A' in
    NNum (20 * n + i) (numberize s 0)
  else
    let i = ord c - ord 'U' in
    numberize s (5 * n + i + 1)
numberize (c : s) _ = NError

data HeapEl = HeapEl Proof | HTerm Label Int | HThm Label Int deriving (Show)

trProof :: Frame -> MMDatabase -> [String] -> Either String ([Label], Proof)
trProof (hs, _) db ("(" : p) =
  processPreloads p (mkHeap hs 0 Q.empty) 0 id where
  mkHeap :: [(Bool, Label)] -> Int -> Q.Seq HeapEl -> Q.Seq HeapEl
  mkHeap [] _ heap = heap
  mkHeap ((_, h):hs) n heap = mkHeap hs (n+1) (heap Q.|> HeapEl (PHyp h n))

  processPreloads :: [String] -> Q.Seq HeapEl -> Int ->
    ([Label] -> [Label]) -> Either String ([Label], Proof)
  processPreloads [] heap sz ds = throwError ("unclosed parens in proof: " ++ show ("(" : p))
  processPreloads (")" : blocks) heap sz ds = do
    pt <- processBlocks (numberize (join blocks) 0) heap 0 []
    return (ds [], pt)
  processPreloads (st : p) heap sz ds = case mStmts db M.!? st of
    Nothing -> throwError ("statement " ++ st ++ " not found")
    Just (Hyp (VHyp s v)) ->
      processPreloads p (heap Q.|> HeapEl (PDummy sz)) (sz + 1) (ds . (s :))
    Just (Hyp (EHyp _ _)) -> throwError "$e found in paren list"
    Just (Term (hs, _) _ _ _) ->
      processPreloads p (heap Q.|> HTerm st (length hs)) sz ds
    Just (Thm (hs, _) _ _ _) ->
      processPreloads p (heap Q.|> HThm st (length hs)) sz ds

  popn :: Int -> [Proof] -> Either String ([Proof], [Proof])
  popn = go [] where
    go stk2 0 stk     = return (stk2, stk)
    go _    n []      = throwError "stack underflow"
    go stk2 n (p:stk) = go (p:stk2) (n-1) stk

  processBlocks :: Numbers -> Q.Seq HeapEl -> Int -> [Proof] -> Either String Proof
  processBlocks NEOF heap sz [pt] = return pt
  processBlocks NEOF _ _ pts = throwError ("bad stack state " ++ show pts)
  processBlocks NError _ _ _ = throwError "proof block parse error"
  processBlocks (NSave p) heap sz [] = throwError "can't save empty stack"
  processBlocks (NSave p) heap sz (pt : pts) =
    processBlocks p (heap Q.|> HeapEl (PBackref sz)) (sz + 1) (PSave pt : pts)
  processBlocks (NSorry p) heap sz pts =
    processBlocks p heap sz (PSorry : pts)
  processBlocks (NNum i p) heap sz pts =
    case heap Q.!? i of
      Nothing -> throwError "proof backref index out of range"
      Just (HeapEl pt) -> processBlocks p heap sz (pt : pts)
      Just (HTerm x n) -> do
        (es, pts') <- withContext (show p) (popn n pts)
        processBlocks p heap sz (PTerm x es : pts')
      Just (HThm x n) -> do
        (es, pts') <- withContext (show p) (popn n pts)
        processBlocks p heap sz (PThm x es : pts')
trProof _ _ _ = throwError "normal proofs not supported"

data JComment =
    JKeyword String JComment
  | JString String JComment
  | JSemi JComment
  | JRest [String]
  | JError String

parseJ :: [String] -> JComment
parseJ [] = JError "unclosed $j comment"
parseJ ("$)" : ss) = JRest ss
parseJ (('\'' : s) : ss) = parseJString s id ss where
  parseJString [] f [] = JError "unclosed $j string"
  parseJString [] f (s:ss) = parseJString s (f . (' ' :)) ss
  parseJString ('\\' : 'n' : s) f ss = parseJString s (f . ('\n' :)) ss
  parseJString ('\\' : '\\' : s) f ss = parseJString s (f . ('\\' :)) ss
  parseJString ('\\' : '\'' : s) f ss = parseJString s (f . ('\'' :)) ss
  parseJString ('\\' : s) f ss = JError ("bad escape sequence '\\" ++ s ++ "'")
  parseJString ('\'' : s) f ss = JString (f []) (parseJ (s : ss))
  parseJString (c : s) f ss = parseJString s (f . (c :)) ss
parseJ (s : ss) = case P.readP_to_S L.lex s of
    [(L.EOF, _)] -> parseJ ss
    [(L.Ident x, s')] -> JKeyword x (parseJ (s' : ss))
    [(L.Punc ";", s')] -> JSemi (parseJ (s' : ss))
    _ -> JError ("parse failed \"" ++ s ++ "\"" ++ head ss)

processJ :: JComment -> FromMMM ()
processJ (JKeyword "syntax" j) = case j of
  JString s (JSemi j') -> addSort s Nothing >> processJ j'
  JString s1 (JKeyword "as" (JString s2 (JSemi j'))) -> do
    addSort s1 (Just s2)
    modifyDB $ \m -> m {mSorts =
      M.adjust (\(s, sd) -> (s, sd {sProvable = True})) s2 (mSorts m)}
    processJ j'
  _ -> throwError "bad $j 'syntax' command"
processJ (JKeyword "bound" j) = case j of
  JString s (JSemi j') -> do
    modifyDB $ \m -> m {mSorts =
      M.adjust (\(s, sd) -> (s, sd {sPure = True})) s (mSorts m)}
    processJ j'
  _ -> throwError "bad $j 'bound' command"
processJ (JKeyword "primitive" j) = processPrim j where
  processPrim (JString s j) = do
    modifyDB $ \m -> m {mPrim = S.insert s (mPrim m)}
    processPrim j
  processPrim (JSemi j) = processJ j
  processPrim _ = throwError "bad $j 'primitive' command"
processJ (JKeyword x j) = skipJ j
processJ (JRest ss) = process ss
processJ (JError e) = throwError e
processJ _ = throwError "bad $j comment"

skipJ :: JComment -> FromMMM ()
skipJ (JSemi j) = processJ j
skipJ (JKeyword _ j) = skipJ j
skipJ (JString _ j) = skipJ j
skipJ (JRest _) = throwError "unfinished $j statement"
skipJ (JError e) = throwError e

ptEmpty :: ParseTrie
ptEmpty = PT M.empty M.empty Nothing

ptInsert :: M.Map Var (Sort, Label) -> ([MMExpr] -> MMExpr) -> Fmla -> Parser -> Parser
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

type ParseResult = [(([MMExpr] -> [MMExpr]) -> MMExpr, [Sym])]
parseFmla :: Fmla -> FromMMM (Const, MMExpr)
parseFmla = \case
  Const s : f -> do
    t <- get
    let s2 = fromMaybe s (fst $ mSorts (mDB t) M.! s)
    e <- fromJustError ("cannot parse formula " ++ show (Const s : f))
      (parseFmla' (mVMap t) (mParser t) s2 f)
    return (s, e)
  f -> throwError ("bad formula" ++ show f)
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
