module MM0.FrontEnd.MathParser (parseFormula, parseFormulaProv, appPrec) where

import Control.Monad.Except
import Control.Monad.Trans.State
import Control.Monad.Reader.Class
import Data.Maybe
import qualified Data.IntMap.Strict as I
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import MM0.FrontEnd.AST
import MM0.Kernel.Environment
import MM0.FrontEnd.ParserEnv
import MM0.FrontEnd.LocalContext
import MM0.Util

type ParserM = StateT [Token] LocalCtxM

parseError :: String -> ParserM a
parseError s = do
  tks <- get
  throwError ("math parse error: " ++ s ++ "; at \"" ++
    concatMap ((++ " ") . T.unpack) (take 5 tks) ++ "...\"")

parseFormulaWith :: ((SExpr, Sort) -> ParserM SExpr) -> Formula -> LocalCtxM SExpr
parseFormulaWith m (Formula fmla) = do
  pe <- readPE
  runStateT (parseExpr 0 >>= m) (tokenize pe fmla) >>= \case
    (sexp, []) -> return sexp
    _ -> throwError "math parse error: expected '$'"

parseFormula :: Sort -> Formula -> LocalCtxM SExpr
parseFormula s = parseFormulaWith (coerce s)

parseFormulaProv :: Formula -> LocalCtxM SExpr
parseFormulaProv = parseFormulaWith (\t -> fst <$> coerceProv t)

tkMatch :: (Token -> Maybe b) -> (Token -> b -> ParserM a) -> ParserM a -> ParserM a
tkMatch f yes no = StateT $ \case
  t : ss -> case f t of
    Nothing -> runStateT no (t : ss)
    Just b -> runStateT (yes t b) ss
  ss -> runStateT no ss

tkCond :: (Token -> Bool) -> ParserM a -> ParserM a -> ParserM a
tkCond p yes no = tkMatch (\t -> if p t then Just () else Nothing) (\_ _ -> yes) no

tk :: Token -> ParserM ()
tk t = tkCond (== t) (return ()) (parseError ("expected '" ++ T.unpack t ++ "'"))

parseVar :: ParserM (SExpr, Sort) -> ParserM (SExpr, Sort)
parseVar no = do
  ctx <- ask
  tkMatch (lookupLocal ctx) (\v (DepType s _) -> return (SVar v, s)) no

parseLiteral :: ParserM (SExpr, Sort) -> ParserM (SExpr, Sort)
parseLiteral no =
  tkCond (== "(") (parseExpr 0 <* tk ")") (parseVar no)

checkPrec :: ParserEnv -> Prec -> Token -> Maybe a -> Maybe a
checkPrec e p v m = do
  q <- prec e M.!? v
  if q >= p then m else Nothing

coerce :: Sort -> (SExpr, Sort) -> ParserM SExpr
coerce s2 (sexp, s1) = do
  pe <- lift readPE
  c <- fromJustError ("type error, expected " ++ T.unpack s2 ++
    ", got " ++ show sexp ++ ": " ++ T.unpack s1) (getCoe s1 s2 pe)
  return (c sexp)

coerceProv :: (SExpr, Sort) -> ParserM (SExpr, Sort)
coerceProv (sexp, s) = do
  pe <- lift readPE
  (s2, c) <- fromJustError ("type error, expected provable sort, got " ++
    show sexp ++ ": " ++ T.unpack s) (getCoeProv s pe)
  return (c sexp, s2)

parseLiterals :: [Sort] -> [PLiteral] -> ParserM [SExpr]
parseLiterals ls = go I.empty where
  go :: I.IntMap SExpr -> [PLiteral] -> ParserM [SExpr]
  go m [] = return (I.elems m)
  go m (PConst t : lits) = tk t >> go m lits
  go m (PVar n p : lits) = do
    e <- parseExpr p >>= coerce (ls !! n)
    go (I.insert n e m) lits

parseLiterals' :: Int -> (SExpr, Sort) -> [Sort] -> [PLiteral] ->
  ParserM (I.IntMap SExpr, Int, (SExpr, Sort))
parseLiterals' n1 lhs ls ll = do
  lhs' <- coerce (ls !! n1) lhs
  go (I.singleton n1 lhs') ll
  where
  go :: I.IntMap SExpr -> [PLiteral] -> ParserM (I.IntMap SExpr, Int, (SExpr, Sort))
  go m [] = throwError "bad literals"
  go m [PVar n p] = (m,n,) <$> parsePrefix p
  go m (PConst t : lits) = tk t >> go m lits
  go m (PVar n p : lits) = do
    e <- parseExpr p >>= coerce (ls !! n)
    go (I.insert n e m) lits

appPrec :: Int
appPrec = 1024

parsePrefix :: Prec -> ParserM (SExpr, Sort)
parsePrefix p = parseLiteral $ do
  pe <- lift readPE
  env <- lift readEnv
  tkMatch (\v -> checkPrec pe p v (prefixes pe M.!? v))
    (\_ (NotaInfo x (_, lits) _) -> do
      let (bs, r) = fromJust (getTerm env x)
      let bss = dSort . binderType <$> bs
      ss <- parseLiterals bss lits
      return (App x ss, dSort r)) $
    tkMatch (\v -> do
        d <- getTerm env v
        if p <= appPrec || null (fst d) then Just d else Nothing)
      (\x (bs, r) -> do
        let bss = dSort . binderType <$> bs
        ss <- mapM (\s -> parsePrefix maxBound >>= coerce s) bss
        return (App x ss, dSort r)) $
    parseError "expected variable or prefix or term s-expr"

getLhs :: Prec -> (SExpr, Sort) -> ParserM (SExpr, Sort)
getLhs p lhs = do
  pe <- lift readPE
  env <- lift readEnv
  tkMatch (\v -> do
      q <- prec pe M.!? v
      if q >= p then (,) q <$> infixes pe M.!? v else Nothing)
    (\_ (q, NotaInfo x (llit, lits) _) -> do
      let (i, _) = fromJust llit
      let (bs, r) = fromJust (getTerm env x)
      let bss = dSort . binderType <$> bs
      (m, n, e) <- parseLiterals' i lhs bss lits
      rhs <- getRhs q e >>= coerce (bss !! n)
      let args = I.elems (I.insert n rhs m)
      getLhs p (App x args, dSort r))
    (return lhs)

getRhs :: Prec -> (SExpr, Sort) -> ParserM (SExpr, Sort)
getRhs p rhs = do
  pe <- lift readPE
  tkMatch (\v -> do
      q <- prec pe M.!? v
      NotaInfo x _ (Just r) <- infixes pe M.!? v
      if (if r then q >= p else q > p) then Just (q, x) else Nothing)
    (\v (q, _) -> modify (v:) >> getLhs q rhs >>= getRhs p)
    (return rhs)

parseExpr :: Prec -> ParserM (SExpr, Sort)
parseExpr p = parsePrefix p >>= getLhs p
