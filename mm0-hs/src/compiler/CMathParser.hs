{-# LANGUAGE BangPatterns #-}
module CMathParser (parseMath, QExpr(..)) where

import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Reader
import Data.Bits
import qualified Data.HashMap.Strict as H
import qualified Data.IntMap as I
import qualified Data.Text as T
import Text.Megaparsec hiding (runParser, unPos)
import Text.Megaparsec.Internal (ParsecT(..))
import CAST
import CEnv hiding (try)
import CParser (Parser, runParser, identStart, identRest, atPos, lispVal)
import MathParser (appPrec)
import Util

data QExpr = QApp (AtPos Ident) [QExpr] | QUnquote (AtPos LispVal) deriving (Show)

type MathParser = ReaderT ParserEnv Parser

parseMath :: Formula -> ElabM QExpr
parseMath (Formula o fmla) = do
  pe <- gets ePE
  let p = takeWhileP Nothing isSpace *> parseExpr (Prec 0) <* (eof <?> "'$'")
      (errs, _, res) = runParser (runReaderT p pe) "" o fmla
  mapM_ (reportErr . toElabError) errs
  fromJust' res

isSpace :: Char -> Bool
isSpace c = c == ' ' || c == '\n'

unquote :: MathParser QExpr
unquote = do
  try (single ',' >> notFollowedBy (satisfy isSpace))
  lift $ QUnquote <$> atPos lispVal

token1 :: MathParser (AtPos T.Text)
token1 = ReaderT $ \pe -> ParsecT $ \s@(State t o pst) cok _ _ eerr ->
  let
    unspace t' o' = State t2 (o'+T.length t1) where
      (t1, t2) = T.span isSpace t'
    go t' i = case T.uncons t' of
      Nothing | i == 0 ->
                eerr (TrivialError (o+i) (pure EndOfInput) mempty) s
              | otherwise ->
                cok (AtPos o (T.take i t)) (State t' (o+i) pst) mempty
      Just (c, t2) -> case delimVal (pDelims pe) c of
        0 -> go t2 (i+1)
        4 | i == 0 ->
            eerr (TrivialError o (Just (Tokens (pure c))) mempty) s
          | otherwise ->
            cok (AtPos o (T.take i t)) (unspace t2 (o+i+1) pst) mempty
        d | testBit d 1 && i /= 0 ->
            cok (AtPos o (T.take i t)) (unspace t' (o+i) pst) mempty
          | testBit d 0 ->
            cok (AtPos o (T.take (i+1) t)) (unspace t2 (o+i+1) pst) mempty
          | otherwise -> go t2 (i+1)
  in go t 0

setErrorOffset :: Offset -> ParseError s e -> ParseError s e
setErrorOffset o (TrivialError _ u p) = TrivialError o u p
setErrorOffset o (FancyError _ x) = FancyError o x

tryAt :: Offset -> MathParser a -> MathParser a
tryAt o (ReaderT p) = ReaderT $ \pe -> ParsecT $ \s cok _ eok eerr ->
  let eerr' err _ = eerr (setErrorOffset o err) s
  in unParser (p pe) s cok eerr' eok eerr'

tkSatisfy :: (T.Text -> Bool) -> MathParser (AtPos T.Text)
tkSatisfy p = try $ do
  at@(AtPos _ t) <- token1
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

isIdent :: T.Text -> Bool
isIdent t = case T.uncons t of
  Nothing -> False
  Just (c, t') -> identStart c && T.all identRest t'

parsePrefix :: Prec -> MathParser QExpr
parsePrefix p =
  unquote <|>
  (tk "(" *> parseExpr (Prec 0) <* tk ")") <|>
  try (do {
    AtPos o v <- token1;
    ((do
      PrefixInfo _ x lits <- tryAt o (checkPrec p True v >>
        asks (H.lookup v . pPrefixes) >>= fromMaybeM)
      QApp (AtPos o x) <$> parseLiterals lits)
      <?> ("prefix >= " ++ show p)) <|>
    ((do
      tryAt o (do
        guard (isIdent v)
        asks (not . H.member v . pPrec) >>= guard)
      QApp (AtPos o v) <$>
        if p <= Prec appPrec && v /= "_" then
          many (parsePrefix PrecMax)
        else return [])
      <?> "identifier") })

getLhs :: Prec -> QExpr -> MathParser QExpr
getLhs p lhs =
  ((do
    AtPos o v <- lookAhead token1
    q <- checkPrec p True v
    InfixInfo _ x _ <- asks (H.lookup v . pInfixes) >>= fromMaybeM
    _ <- token1
    rhs <- parsePrefix p >>= getRhs q
    getLhs p (QApp (AtPos o x) [lhs, rhs]))
    <?> ("infix >= " ++ show p)) <|>
  return lhs

getRhs :: Prec -> QExpr -> MathParser QExpr
getRhs p rhs =
  (do
    AtPos _ v <- lookAhead token1
    InfixInfo _ _ r <- asks (H.lookup v . pInfixes) >>= fromMaybeM
    (do q <- checkPrec p r v
        getLhs q rhs >>= getRhs p)
      <?> ("infix " ++ (if r then ">= " else "> ") ++ show p)) <|>
  return rhs

parseExpr :: Prec -> MathParser QExpr
parseExpr p = parsePrefix p >>= getLhs p
