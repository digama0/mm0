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
import qualified AST as A

fromMM :: [String] -> IO ()
fromMM [] = die "from-mm: no .mm file specified"
fromMM (mm:rest) = do
  s <- openFile mm ReadMode >>= B.hGetContents
  db <- liftIO (parseMM s)
  ast <- liftIO $ makeAST db
  hSetNewlineMode stdout (NewlineMode LF LF)
  mapM_ (\d -> putStrLn $ shows d "\n") ast

data ParseTrie = PT {
  ptConst :: Parser,
  ptVar :: M.Map Sort ParseTrie,
  ptDone :: Maybe (Sort, [SExpr] -> SExpr) }
type Parser = M.Map Const ParseTrie

ptEmpty :: ParseTrie
ptEmpty = PT M.empty M.empty Nothing

ptInsert :: M.Map Var (Sort, Ident) -> ([SExpr] -> SExpr) -> Fmla -> Parser -> Parser
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

reorderMap :: M.Map Var Int -> Fmla -> [SExpr] -> [SExpr]
reorderMap m f = let l = I.elems (buildIM f 0 I.empty) in \es -> map (es !!) l where
  buildIM :: Fmla -> Int -> I.IntMap Int -> I.IntMap Int
  buildIM [] _ i = i
  buildIM (Const _ : f) n i = buildIM f n i
  buildIM (Var v : f) n i = buildIM f (n+1) (I.insert (m M.! v) n i)

data TransState = TransState {
  tParser :: Parser,
  tVMap :: M.Map Var (Sort, Ident),
  tParsedHyps :: M.Map Label SExpr,
  tNameMap :: M.Map Label Ident,
  tUsedNames :: S.Set Ident }

type TransM = RWST MMDatabase (Endo A.AST) TransState (Either String)

runTransM :: TransM a -> MMDatabase -> Either String (a, A.AST)
runTransM m db = do
  (a, Endo f) <- evalRWST m db (TransState M.empty M.empty M.empty M.empty S.empty)
  return (a, A.Notation (A.Delimiter $ A.Const $ C.pack " ( ) ") : f [])

makeAST :: MMDatabase -> Either String A.AST
makeAST db = snd <$> runTransM (mapM_ trDecl (mDecls db)) db

emit :: A.Stmt -> TransM ()
emit d = tell (Endo (d :))

type ParseResult = [(([SExpr] -> [SExpr]) -> SExpr, [Sym])]
parseFmla :: Fmla -> TransM SExpr
parseFmla = \case
  Const s : f -> do
    t <- get
    db <- ask
    let s2 = fromMaybe s (fst $ mSorts db M.! s)
    fromJustError (error ("cannot parse formula " ++ show (Const s : f)))
      (parseFmla' (tVMap t) (tParser t) s2 f)
  f -> error ("bad formula" ++ show f)
  where
  parseFmla' :: M.Map Var (Sort, Ident) -> Parser -> Sort -> [Sym] -> Maybe SExpr
  parseFmla' vm p = \s f -> parseEOF (parse s p f) where
    parseEOF :: [(SExpr, [Sym])] -> Maybe SExpr
    parseEOF [] = Nothing
    parseEOF ((e, []) : _) = Just e
    parseEOF (_ : es) = parseEOF es
    parse :: Sort -> Parser -> [Sym] -> [(SExpr, [Sym])]
    parse s p f = (case f of
      Var v : f' -> let (s', v') = vm M.! v in
        if s == s' then [(SVar v', f')] else []
      _ -> []) ++ ((\(g, f') -> (g id, f')) <$> parseC s p s f)
    parseC :: Sort -> Parser -> Const -> [Sym] -> ParseResult
    parseC s q c f = parsePT s f (M.findWithDefault ptEmpty c q)
    parseD :: Sort -> Maybe (Sort, [SExpr] -> SExpr) -> [Sym] -> ParseResult
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
    (Nothing, sd) -> emit (A.Sort s sd)
    _ -> return ()
  Stmt st -> case mStmts db M.! st of
    Hyp (VHyp c v) -> do
      i <- trName st (if identStr v then v else mangle st)
      modify $ \m -> m {tVMap = M.insert v (c, i) (tVMap m)}
    Hyp (EHyp f) -> do
      e <- parseFmla f
      modify $ \m -> m {tParsedHyps = M.insert st e (tParsedHyps m)}
    Thm fr f@(Const s : _) [] | isNothing (fst (mSorts db M.! s)) -> do
      (bs, reord) <- splitFrame fr
      i <- trName st (mangle st)
      let g = App i . reorderMap reord f
      modify $ \m -> m {tParser = ptInsert (tVMap m) g f (tParser m)}
      emit (A.Term i bs (DepType s []))
    Thm fr f@(Const s : _) p -> do
      (bs, _) <- splitFrame fr
      e <- parseFmla f
      i <- trName st (mangle st)
      case p of
        [] -> emit (A.Axiom i bs (exprToFmla e))
        _ -> emit (A.Theorem i bs (exprToFmla e))
    Thm _ _ _ -> throwError "bad theorem statement"
  where
  splitFrame :: Frame -> TransM ([A.Binder], M.Map Var Int)
  splitFrame (hs, ds) = do db <- ask; t <- get; splitFrame' hs ds db t
  splitFrame' hs ds db t = do
      (vs, bs, hs') <- go hs
      return (
        map (\(v, v', s) -> A.Binder (A.LBound v') $ A.TType $ DepType s []) vs ++
        map (\(v, v', s) -> A.Binder (A.LReg v') $ A.TType $ DepType s $
          mapMaybe (\(v2, v2', _) -> if memDVs ds v v2 then Just v2' else Nothing) vs) bs ++
        hs', buildReorder (vs ++ bs) 0 M.empty)
    where
    go :: [Label] -> TransM ([(Var, Ident, Sort)], [(Var, Ident, Sort)], [A.Binder])
    go (l : ls) = case mStmts db M.! l of
        Hyp (VHyp s v) -> do
          (vs, bs, hs) <- go ls
          v' <- trName l (if identStr v then v else mangle l)
          if sPure (snd (mSorts db M.! s)) then return ((v, v', s) : vs, bs, hs)
          else return (vs, (v, v', s) : bs, hs)
        Hyp (EHyp f) -> do
          let e = tParsedHyps t M.! l
          (vs, bs, hs) <- go ls
          return (vs, bs, A.Binder (A.LReg l) (A.TFormula $ exprToFmla e) : hs)
    go [] = return ([], [], [])

    buildReorder :: [(Var, Ident, Sort)] -> Int -> M.Map Var Int -> M.Map Var Int
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
