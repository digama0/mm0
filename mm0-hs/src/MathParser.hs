module MathParser(parseFormula) where

import Control.Monad.Except
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.State
import Control.Monad.Reader.Class
import Data.List
import Data.List.Split
import Data.Maybe
import qualified Data.IntMap.Strict as I
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.ByteString.Char8 as C
import AST
import Environment
import ParserEnv
import LocalContext
import Util

type ParserM = StateT [Token] LocalCtxM

parseError :: MonadError String m => String -> m a
parseError s = throwError ("math parse error: " ++ s)

parseFormula :: Formula -> LocalCtxM SExpr
parseFormula s = do
  pe <- readPE
  runStateT (parseExpr 0) (tokenize pe s) >>= \case
    ((sexp, _), []) -> return sexp
    _ -> parseError "expected $"

tkMatch :: (Token -> Maybe b) -> (Token -> b -> ParserM a) -> ParserM a -> ParserM a
tkMatch f yes no = StateT $ \case
  t : ss -> case f t of
    Nothing -> runStateT no ss
    Just b -> runStateT (yes t b) ss
  ss -> runStateT no ss

tkCond :: (Token -> Bool) -> ParserM a -> ParserM a -> ParserM a
tkCond p yes no = tkMatch (\t -> if p t then Just () else Nothing) (\_ _ -> yes) no

tk :: Token -> ParserM ()
tk t = tkCond (== t) (return ()) (parseError ("expected " ++ t))

parseVar :: ParserM (SExpr, Ident) -> ParserM (SExpr, Ident)
parseVar no = do
  ctx <- ask
  stk <- lift readStack
  tkMatch (\v -> lookupVarSort stk ctx v)
    (\v s -> return (SVar v, s)) no

parseLiteral :: ParserM (SExpr, Ident) -> ParserM (SExpr, Ident)
parseLiteral no =
  tkCond (== "(") (parseExpr 0 <* tk ")") (parseVar no)

checkPrec :: ParserEnv -> Prec -> Token -> Maybe a -> Maybe a
checkPrec e p v m = do
  q <- prec e M.!? v
  if q >= p then m else Nothing

coerce :: Ident -> (SExpr, Ident) -> ParserM SExpr
coerce s2 (sexp, s1) = do
  pe <- lift readPE
  c <- fromJustError ("type error, expected " ++ s2 ++ ", got " ++ s1) (getCoe s1 s2 pe)
  return (c sexp)

parseLiterals :: [Ident] -> [PLiteral] -> ParserM [SExpr]
parseLiterals ls = go I.empty where
  go m [] = return (I.elems m)
  go m (PConst t : lits) = tk t >> go m lits
  go m (PVar n p : lits) = do
    e <- parseExpr p >>= coerce (ls !! n)
    go (I.insert n e m) lits

appPrec :: Int
appPrec = 1024

parseSExpr :: Ident -> ParserM SExpr
parseSExpr s = parseLiteral (parseError "expected s-expr") >>= coerce s

parsePrefix :: Prec -> ParserM (SExpr, Ident)
parsePrefix p = parseLiteral $ do
  pe <- lift readPE
  env <- lift readEnv
  tkMatch (\v -> checkPrec pe p v (prefixes pe M.!? v))
    (\v (PrefixInfo x lits) -> do
      let (as, bs, r) = fromJust (getTerm env v)
      ss <- parseLiterals ((snd <$> as) ++ (dSort <$> bs)) lits
      return (App x ss, dSort r)) $
    tkMatch (\v -> if p < appPrec then Nothing else getTerm env v)
      (\x (as, bs, r) -> do
        ss <- mapM parseSExpr ((snd <$> as) ++ (dSort <$> bs))
        return (App x ss, dSort r)) $
    parseError "expected expression"

getLhs :: Prec -> (SExpr, Ident) -> ParserM (SExpr, Ident)
getLhs p lhs = do
  pe <- lift readPE
  env <- lift readEnv
  tkMatch (\v -> do
      q <- prec pe M.!? v
      if q >= p then (,) q <$> infixes pe M.!? v else Nothing)
    (\v (q, InfixInfo x _) -> do
      rhs <- parsePrefix p >>= getRhs q
      let (as, bs, r) = fromJust (getTerm env v)
      let [s1, s2] = (snd <$> as) ++ (dSort <$> bs)
      lhs' <- coerce s1 lhs
      rhs' <- coerce s2 rhs
      getLhs p (App x [lhs', rhs'], dSort r))
    (return lhs)

getRhs :: Prec -> (SExpr, Ident) -> ParserM (SExpr, Ident)
getRhs p rhs = do
  pe <- lift readPE
  env <- lift readEnv
  tkMatch (\v -> do
      q <- prec pe M.!? v
      InfixInfo x r <- infixes pe M.!? v
      if (if r then q >= p else q > p) then Just (q, x) else Nothing)
    (\v (q, x) -> modify (v:) >> getLhs q rhs >>= getRhs p)
    (return rhs)


parseExpr :: Prec -> ParserM (SExpr, Ident)
parseExpr = \p -> parsePrefix p >>= getLhs p
