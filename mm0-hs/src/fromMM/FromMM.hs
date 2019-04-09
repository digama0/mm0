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
  putStrLn $ show (M.size (mStmts db)) ++ " statements"
  ast <- liftIO $ makeAST db
  putStrLn $ show ast

data ParseTrie = PT {
  ptConst :: Parser,
  ptVar :: M.Map Sort ParseTrie,
  ptDone :: Maybe (Sort, Label) } deriving (Show)
type Parser = M.Map Const ParseTrie

ptEmpty :: ParseTrie
ptEmpty = PT M.empty M.empty Nothing

ptInsert :: M.Map Var (Sort, Label) -> Label -> Fmla -> Parser -> Parser
ptInsert vm x (Const s : f) = insert1 s f where
  insert1 :: String -> [Sym] -> Parser -> Parser
  insert1 i f = M.alter (Just . insertPT f . fromMaybe ptEmpty) i
  insertPT :: [Sym] -> ParseTrie -> ParseTrie
  insertPT [] (PT cs vs Nothing) = PT cs vs (Just (s, x))
  insertPT [] (PT _ _ _) = error "duplicate parser"
  insertPT (Const c : f) (PT cs vs d) = PT (insert1 c f cs) vs d
  insertPT (Var v : f) (PT cs vs d) =
    PT cs (insert1 (fst (fromJust (vm M.!? v))) f vs) d
ptInsert _ x _ = error ("bad decl " ++ x)

data TransState = TransState {
  tParser :: Parser,
  tVMap :: M.Map Var (Sort, Label),
  tParsedHyps :: M.Map Label SExpr }

type TransM = RWST MMDatabase (Endo A.AST) TransState (Either String)

runTransM :: TransM a -> MMDatabase -> Either String (a, A.AST)
runTransM m db = do
  (a, Endo f) <- evalRWST m db (TransState M.empty M.empty M.empty)
  return (a, f [])

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
    let s2 = fromMaybe s (fst $ fromJust $ mSorts db M.!? s)
    fromJustError (error ("cannot parse formula " ++ show (Const s : f)))
      (parseFmla' (tVMap t) (tParser t) s2 f)
  f -> error ("bad formula" ++ show f)
  where
  parseFmla' :: M.Map Var (Sort, Label) -> Parser -> Sort -> [Sym] -> Maybe SExpr
  parseFmla' vm p = \s f -> parseEOF (parse s p f) where
    parseEOF :: [(SExpr, [Sym])] -> Maybe SExpr
    parseEOF [] = Nothing
    parseEOF ((e, []) : _) = Just e
    parseEOF (_ : es) = parseEOF es
    parse :: Sort -> Parser -> [Sym] -> [(SExpr, [Sym])]
    parse s p f = (case f of
      Var v : f' | fst (vm M.! v) == s -> [(SVar v, f')]
      _ -> []) ++ ((\(g, f') -> (g id, f')) <$> parseC s p s f)
    parseC :: Sort -> Parser -> Const -> [Sym] -> ParseResult
    parseC s q c f = parsePT s f (M.findWithDefault ptEmpty c q)
    parseD :: Sort -> Maybe (Sort, Label) -> [Sym] -> ParseResult
    parseD s (Just (s', l)) f | s' == s = [(\g -> App l (g []), f)]
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
  Sort s -> case fromJust $ mSorts db M.!? s of
    (Nothing, sd) -> emit (A.Sort s sd)
    _ -> return ()
  Stmt st -> case fromJust $ mStmts db M.!? st of
    Hyp (VHyp c v) ->
      modify $ \m -> m {tVMap = M.insert v (c, st) (tVMap m)}
    Hyp (EHyp f) -> do
      e <- parseFmla f
      modify $ \m -> m {tParsedHyps = M.insert st e (tParsedHyps m)}
    Thm fr f@(Const s : _) [] | isNothing (fst (fromJust $ mSorts db M.!? s)) -> do
      bs <- splitFrame fr
      modify $ \m -> m {tParser = ptInsert (tVMap m) st f (tParser m)}
      emit (A.Term st bs (DepType s []))
    Thm fr f@(Const s : _) p -> do
      bs <- splitFrame fr
      e <- parseFmla f
      case p of
        [] -> emit (A.Axiom st bs (C.pack $ show e))
        _ -> emit (A.Theorem st bs (C.pack $ show e))
    Thm _ _ _ -> throwError "bad theorem statement"
  where
  splitFrame :: Frame -> TransM [A.Binder]
  splitFrame (hs, ds) = splitFrame' hs ds <$> ask <*> get
  splitFrame' hs ds db t = go hs [] [] [] where
    go :: [Label] -> [(Var, Sort)] -> [(Var, Sort)] -> [A.Binder] -> [A.Binder]
    go (l:ls) vs bs hs = case fromJust (mStmts db M.!? l) of
        Hyp (VHyp s v) ->
          if sPure (snd (fromJust $ mSorts db M.!? s)) then go ls ((v, s) : vs) bs hs
          else go ls vs ((v, s) : bs) hs
        Hyp (EHyp f) ->
          let e = fromJust (tParsedHyps t M.!? l) in
          go ls vs bs (A.Binder (A.LReg l) (A.TFormula $ C.pack $ show e) : hs)
    go [] vs bs hs =
      map (\(v, s) -> A.Binder (A.LBound v) $ A.TType $ DepType s []) vs ++
      map (\(v, s) -> A.Binder (A.LReg v) $ A.TType $ DepType s $
        filter (not . memDVs ds v) (fst <$> vs)) bs ++ hs
