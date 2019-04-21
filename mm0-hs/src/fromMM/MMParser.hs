module MMParser (parseMM) where

import Data.List
import Data.Char
import Control.Monad.Trans.State
import Control.Monad.Except hiding (liftIO)
import qualified Text.ParserCombinators.ReadP as P
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString.Lazy.Char8 as C
import qualified Text.Read.Lex as L
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Sequence as Q
import Environment (SortData(..))
import MMTypes
import Util

parseMM :: B.ByteString -> Either String MMDatabase
parseMM s = snd <$> runFromMMM (process (toks s))

toks :: B.ByteString -> [String]
toks = filter (not . null) . map C.unpack .
  C.splitWith (`elem` [' ', '\n', '\t', '\r'])

type FromMMM = StateT MMDatabase (Either String)

withContext :: MonadError String m => String -> m a -> m a
withContext s m = catchError m (\e -> throwError ("at " ++ s ++ ": " ++ e))

runFromMMM :: FromMMM a -> Either String (a, MMDatabase)
runFromMMM m = runStateT m $
  MMDatabase M.empty Q.empty S.empty M.empty M.empty [([], [], S.empty)]

addConstant :: Const -> FromMMM ()
addConstant c = modify (\s -> s {mSyms = M.insert c (Const c) (mSyms s)})

addVariable :: Var -> FromMMM ()
addVariable v = modify (\s -> s {mSyms = M.insert v (Var v) (mSyms s)})

fmlaVars :: Fmla -> S.Set String
fmlaVars [] = S.empty
fmlaVars (Const _ : ss) = fmlaVars ss
fmlaVars (Var v : ss) = S.insert v (fmlaVars ss)

scopeAddHyp :: Label -> Hyp -> Scope -> Scope
scopeAddHyp x h ((hs, ds, vs) : s) = ((x, h):hs, ds, vs') : s where
  vs' = case h of
    EHyp f -> S.union (fmlaVars f) vs
    _ -> vs

scopeAddDV :: [Var] -> Scope -> Scope
scopeAddDV ds' ((hs, ds, vs) : s) = (hs, ds' : ds, vs) : s

scopeOpen :: Scope -> Scope
scopeOpen ss@((_, _, vs) : _) = ([], [], vs) : ss

scopeClose :: Scope -> Maybe Scope
scopeClose (_ : []) = Nothing
scopeClose (_ : s : ss) = Just (s : ss)

addHyp :: Label -> Hyp -> FromMMM ()
addHyp x h = do
  addStmt x (Hyp h)
  modify $ \s -> s {mScope = scopeAddHyp x h (mScope s)}

mkFrame :: Fmla -> FromMMM Frame
mkFrame = \fmla -> do
  g <- get
  let sc@((_, _, vs) : _) = mScope g
  return (build (S.union vs (fmlaVars fmla)) sc ([], S.empty))

build :: S.Set Var -> Scope -> Frame -> Frame
build vars = go where
  go [] fr = fr
  go ((hs, ds, vs) : sc) (hs', ds') =
    go sc (insertHyps hs hs', foldl' insertDVs ds' ds)

  insertHyps :: [(Label, Hyp)] -> [String] -> [String]
  insertHyps [] hs' = hs'
  insertHyps ((s, EHyp _):hs) hs' = insertHyps hs (s:hs')
  insertHyps ((s, VHyp _ v):hs) hs' =
    insertHyps hs (if S.member v vars then s:hs' else hs')

  insertDVs :: DVs -> [Var] -> DVs
  insertDVs ds [] = ds
  insertDVs ds (v:vs) = let ds' = insertDVs ds vs in
    if S.member v vars then foldl' (insertDV1 v) ds' vs else ds'

  insertDV1 :: Var -> DVs -> Var -> DVs
  insertDV1 v1 ds v2 =
    if S.member v2 vars then
      S.insert (if v1 < v2 then (v1, v2) else (v2, v1)) ds
    else ds

addSort :: Sort -> Maybe Sort -> FromMMM ()
addSort x s2 = modify $ \m -> m {
  mSorts = M.insert x (s2, SortData False False False False) (mSorts m),
  mDecls = mDecls m Q.|> Sort x }

addStmt :: Label -> Stmt -> FromMMM ()
addStmt x st = modify $ \s -> s {
  mDecls = mDecls s Q.|> Stmt x,
  mStmts = M.insert x st (mStmts s) }

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
  modify $ \s -> s {mScope = scopeAddDV vs (mScope s)}
  process ss'
process ("${" : ss) = do
  modify $ \s -> s {mScope = scopeOpen (mScope s)}
  process ss
process ("$}" : ss) = do
  s <- get
  sc <- fromJustError "too many $}" (scopeClose (mScope s))
  put (s {mScope = sc})
  process ss
process (x : "$f" : c : v : "$." : ss) = addHyp x (VHyp c v) >> process ss
process (x : "$e" : ss) = do
  (f, ss') <- withContext x $ readMath "$." ss
  withContext x $ addHyp x (EHyp f)
  process ss'
process (x : "$a" : ss) = do
  (f, ss') <- withContext x $ readMath "$." ss
  withContext x $ do
    fr <- mkFrame f
    addStmt x (Thm fr f Nothing)
  process ss'
process (x : "$p" : ss) = do
  (f, ss1) <- withContext x $ readMath "$=" ss
  fr <- withContext x $ mkFrame f
  (p, ss2) <- withContext x $ readProof ss1
  withContext x $ do
    (p, ss2) <- readProof ss1
    db <- get
    pr <- lift $ trProof fr db p
    addStmt x (Thm fr f (Just pr))
  process ss2
process (x : ss) = throwError ("wtf " ++ x ++ show (take 100 ss))

readUntil :: String -> [String] -> FromMMM ([String], [String])
readUntil u = go id where
  go f [] = throwError "unclosed command"
  go f ("$(" : ss) = readUntil "$)" ss >>= go f . snd
  go f (s : ss) | s == u = return (f [], ss)
  go f (s : ss) = go (f . (s:)) ss

readMath :: String -> [String] -> FromMMM (Fmla, [String])
readMath u ss = do
  (sy, ss') <- readUntil u ss
  m <- get
  f <- mapM (\s ->
    fromJustError ("unknown symbol '" ++ s ++ "'") (mSyms m M.!? s)) sy
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

data HeapEl = HeapEl Proof | HThm Label Int deriving (Show)

trProof :: Frame -> MMDatabase -> [String] -> Either String ([Label], Proof)
trProof (hs, _) db ("(" : p) =
  processPreloads p (mkHeap hs 0 Q.empty) 0 id where
  mkHeap :: [Label] -> Int -> Q.Seq HeapEl -> Q.Seq HeapEl
  mkHeap [] _ heap = heap
  mkHeap (h:hs) n heap = mkHeap hs (n+1) (heap Q.|> HeapEl (PHyp h n))

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
    Just (Hyp (EHyp _)) -> throwError "$e found in paren list"
    Just (Thm (hs, _) _ _) ->
      processPreloads p (heap Q.|> HThm st (length hs)) sz ds

  popn :: Int -> [Proof] -> Either String ([Proof], [Proof])
  popn = go [] where
    go stk2 0 stk     = return (stk2, stk)
    go _    n []      = throwError "stack underflow"
    go stk2 n (p:stk) = go (p:stk2) (n-1) stk

  processBlocks :: Numbers -> Q.Seq HeapEl -> Int -> [Proof] -> Either String Proof
  processBlocks NEOF heap sz [pt] = return pt
  processBlocks NEOF _ _ _ = throwError "bad stack state"
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
    modify $ \m -> m {mSorts =
      M.adjust (\(s, sd) -> (s, sd {sProvable = True})) s2 (mSorts m)}
    processJ j'
  _ -> throwError "bad $j 'syntax' command"
processJ (JKeyword "bound" j) = case j of
  JString s (JSemi j') -> do
    modify $ \m -> m {mSorts =
      M.adjust (\(s, sd) -> (s, sd {sPure = True})) s (mSorts m)}
    processJ j'
  _ -> throwError "bad $j 'bound' command"
processJ (JKeyword "primitive" j) = processPrim j where
  processPrim (JString s j) = do
    modify $ \m -> m {mPrim = S.insert s (mPrim m)}
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
