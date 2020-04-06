{-# LANGUAGE BangPatterns #-}
module MM0.Compiler.MathParser (parseMath, QExpr(..)) where

import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Data.Maybe
import qualified Data.HashMap.Strict as H
import qualified Data.IntMap as I
import qualified Data.Text as T
import Text.Megaparsec hiding (runParser, unPos)
import Text.Megaparsec.Internal (ParsecT(..))
import MM0.Compiler.AST
import MM0.Compiler.Env hiding (try)
import MM0.Compiler.Parser (Parser, runParser, identStart, identRest, lispVal)
import MM0.FrontEnd.MathParser (appPrec)
import MM0.Util

type MathParser = ReaderT ParserEnv Parser

parseMath :: Formula -> ElabM QExpr
parseMath (Formula o fmla) = do
  pe <- gets ePE
  let p = takeWhileP Nothing isSpace *> parseExpr (Prec 0) <* (eof <?> "'$'")
      (errs, _, res) = runParser (runReaderT p pe) "" o fmla
  mode <- gets eReportMode
  fp <- asks efName
  mapM_ (reportErr' . toElabError mode fp) errs
  r <- fromJust' res
  modify $ \env -> env {eParsedFmlas = I.insert o r (eParsedFmlas env)}
  return r

isSpace :: Char -> Bool
isSpace c = c == ' ' || c == '\n'

unquote :: MathParser QExpr
unquote = do
  try (single ',' >> notFollowedBy (satisfy isSpace))
  lift $ QUnquote <$> lispVal

token1 :: MathParser (Span T.Text)
token1 = ReaderT $ \pe -> ParsecT $ \s@(State t o pst) cok _ _ eerr ->
  let
    unspace t' o' = State t2 (o'+T.length t1) where
      (t1, t2) = T.span isSpace t'
    go t' i = case T.uncons t' of
      Nothing | i == 0 ->
                eerr (TrivialError (o+i) (pure EndOfInput) mempty) s
              | otherwise ->
                cok (Span (o, o+i) (T.take i t)) (State t' (o+i) pst) mempty
      Just (c, t2) -> case delimVal (pDelims pe) c of
        0 -> go t2 (i+1)
        4 | i == 0 ->
            eerr (TrivialError o (Just (Tokens (pure c))) mempty) s
          | otherwise ->
            cok (Span (o, o+i) (T.take i t)) (unspace t2 (o+i+1) pst) mempty
        d | isRightDelim d && i /= 0 ->
            cok (Span (o, o+i) (T.take i t)) (unspace t' (o+i) pst) mempty
          | isLeftDelim d ->
            cok (Span (o, o+i+1) (T.take (i+1) t)) (unspace t2 (o+i+1) pst) mempty
          | otherwise -> go t2 (i+1)
  in go t 0

setErrorOffset :: Offset -> ParseError s e -> ParseError s e
setErrorOffset o (TrivialError _ u p) = TrivialError o u p
setErrorOffset o (FancyError _ x) = FancyError o x

tryAt :: Offset -> MathParser a -> MathParser a
tryAt o (ReaderT p) = ReaderT $ \pe -> ParsecT $ \s cok _ eok eerr ->
  let eerr' err _ = eerr (setErrorOffset o err) s
  in unParser (p pe) s cok eerr' eok eerr'

tkSatisfy :: (T.Text -> Bool) -> MathParser (Span T.Text)
tkSatisfy p = try $ do
  at@(Span _ t) <- token1
  guard (p t)
  return at

tk :: T.Text -> MathParser ()
tk t = label (T.unpack t) $ () <$ tkSatisfy (== t)

checkPrec :: Prec -> Bool -> T.Text -> MathParser Prec
checkPrec p r v = do
  (_, q) <- asks (H.lookup v . pPrec) >>= fromMaybeM
  guard (if r then q >= p else q > p)
  return q

parseLiterals :: [PLiteral] -> MathParser [QExpr]
parseLiterals = go I.empty where
  go :: I.IntMap QExpr -> [PLiteral] -> MathParser [QExpr]
  go m [] = return (I.elems m)
  go m (PConst t : lits) = tk t >> go m lits
  go m (PVar n p : lits) = do
    e <- parseExpr p
    go (I.insert n e m) lits

parseLiterals' :: Int -> QExpr -> [PLiteral] ->
  MathParser (I.IntMap QExpr, Int, QExpr)
parseLiterals' n1 lhs ll = go (I.singleton n1 lhs) ll where
  go :: I.IntMap QExpr -> [PLiteral] -> MathParser (I.IntMap QExpr, Int, QExpr)
  go _ [] = error "bad literals"
  go m [PVar n p] = (m,n,) <$> parsePrefix p
  go m (PConst t : lits) = tk t >> go m lits
  go m (PVar n p : lits) = do
    e <- parseExpr p
    go (I.insert n e m) lits

isIdent :: T.Text -> Bool
isIdent t = case T.uncons t of
  Nothing -> False
  Just (c, t') -> identStart c && T.all identRest t'

parsePrefix :: Prec -> MathParser QExpr
parsePrefix p =
  unquote <|>
  (tk "(" *> parseExpr (Prec 0) <* tk ")") <|>
  try (do {
    Span o@(o1, _) v <- token1;
    ((do
      NotaInfo _ x (_, lits) _ <- tryAt o1 (checkPrec p True v >>
        asks (H.lookup v . pPrefixes) >>= fromMaybeM)
      QApp (Span o x) <$> parseLiterals lits)
      <?> ("prefix >= " ++ show p)) <|>
    ((do
      tryAt o1 (do
        guard (isIdent v)
        asks (not . H.member v . pPrec) >>= guard)
      QApp (Span o v) <$>
        if p <= Prec appPrec && v /= "_" then
          many (parsePrefix PrecMax)
        else return [])
      <?> "identifier") })

getLhs :: Prec -> QExpr -> MathParser QExpr
getLhs p lhs =
  ((do
    Span o v <- lookAhead token1
    q <- checkPrec p True v
    NotaInfo _ x (llit, lits) _ <- asks (H.lookup v . pInfixes) >>= fromMaybeM
    let (i, _) = fromJust llit
    _ <- token1
    (m, n, e) <- parseLiterals' i lhs lits
    rhs <- getRhs q e
    let args = I.elems (I.insert n rhs m)
    getLhs p (QApp (Span o x) args))
    <?> ("infix >= " ++ show p)) <|>
  return lhs

getRhs :: Prec -> QExpr -> MathParser QExpr
getRhs p rhs =
  (do
    Span _ v <- lookAhead token1
    NotaInfo _ _ _ (Just r) <- asks (H.lookup v . pInfixes) >>= fromMaybeM
    (do q <- checkPrec p r v
        getLhs q rhs >>= getRhs p)
      <?> ("infix " ++ (if r then ">= " else "> ") ++ show p)) <|>
  return rhs

parseExpr :: Prec -> MathParser QExpr
parseExpr p = parsePrefix p >>= getLhs p
