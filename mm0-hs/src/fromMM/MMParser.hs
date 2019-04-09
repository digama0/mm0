module MMParser (parseMM) where

import Debug.Trace
import Data.List
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
  MMDatabase M.empty Q.empty S.empty M.empty M.empty [([], [])]

addConstant :: Const -> FromMMM ()
addConstant c = modify (\s -> s {mSyms = M.insert c (Const c) (mSyms s)})

addVariable :: Var -> FromMMM ()
addVariable v = modify (\s -> s {mSyms = M.insert v (Var v) (mSyms s)})

scopeAddHyp :: Label -> Hyp -> Scope -> Scope
scopeAddHyp x h ((hs, ds) : s) = ((x, h):hs, ds) : s

scopeAddDV :: [Var] -> Scope -> Scope
scopeAddDV ds' ((hs, ds) : s) = (hs, ds' : ds) : s

scopeOpen :: Scope -> Scope
scopeOpen ss = ([], []) : ss

scopeClose :: Scope -> Maybe Scope
scopeClose (_ : []) = Nothing
scopeClose (_ : s : ss) = Just (s : ss)

addHyp :: Label -> Hyp -> FromMMM ()
addHyp x h = do
  addStmt x (Hyp h)
  modify $ \s -> s {mScope = scopeAddHyp x h (mScope s)}

fmlaVars :: Fmla -> S.Set String
fmlaVars [] = S.empty
fmlaVars (Const _ : ss) = fmlaVars ss
fmlaVars (Var v : ss) = S.insert v (fmlaVars ss)

mkFrame :: Fmla -> FromMMM Frame
mkFrame fmla = do g <- get; return (build (mScope g) ([], S.empty)) where
  vars = fmlaVars fmla
  build :: Scope -> Frame -> Frame
  build [] fr = fr
  build ((hs, ds) : sc) (hs', ds') =
    build sc (insertHyps hs hs', foldl' insertDVs ds' ds)

  insertHyps :: [(Label, Hyp)] -> [String] -> [String]
  insertHyps [] hs' = hs'
  insertHyps ((s, EHyp _):hs) hs' = insertHyps hs (s:hs')
  insertHyps ((s, VHyp _ v):hs) hs' =
    insertHyps hs (if S.member v vars then s:hs' else hs')

  insertDVs :: DVs -> [Var] -> DVs
  insertDVs ds [] = ds
  insertDVs ds (v:vs) =
    if S.member v vars then insertDV1 v vs ds else ds

  insertDV1 :: Var -> [Var] -> DVs -> DVs
  insertDV1 v [] ds = ds
  insertDV1 v1 (v2:vs) ds =
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
    addStmt x (Thm fr f [])
  process ss'
process (x : "$p" : ss) = do
  (f, ss1) <- withContext x $ readMath "$=" ss
  fr <- withContext x $ mkFrame f
  (p, ss2) <- withContext x $ readProof ss1
  withContext x $ do
    (p, ss2) <- readProof ss1
    addStmt x (Thm fr f p)
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
processJ (JKeyword x j) = trace ("unknown $j " ++ x) (skipJ j)
processJ (JRest ss) = process ss
processJ (JError e) = throwError e
processJ _ = throwError "bad $j comment"

skipJ :: JComment -> FromMMM ()
skipJ (JSemi j) = processJ j
skipJ (JKeyword _ j) = skipJ j
skipJ (JString _ j) = skipJ j
skipJ (JRest _) = throwError "unfinished $j statement"
skipJ (JError e) = throwError e
