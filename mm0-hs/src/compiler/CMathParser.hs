{-# LANGUAGE BangPatterns #-}
module CMathParser (parseMath) where

import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class
import Data.Void
import Data.Bits
import qualified Data.HashMap.Strict as H
import qualified Data.List.NonEmpty as NE
import qualified Data.IntMap as I
import qualified Data.Vector as V
import qualified Data.Text as T
import Text.Megaparsec hiding (runParser, try, unPos)
import Text.Megaparsec.Internal (ParsecT(..))
import CAST
import CEnv
import CParser (Parser, runParser, identStart, identRest, lispVal)
import MathParser (appPrec)
import Util

data QExpr = QApp (AtPos Ident) [QExpr] | QUnquote LispVal

type MathParser = ReaderT ParserEnv Parser

parseMath :: Formula -> ElabM QExpr
parseMath (Formula o fmla) = do
  pe <- gets ePE
  let p = parseExpr 0 <* (eof <?> "'$'")
      (errs, o', res) = runParser (runReaderT p pe) "" o fmla
  mapM_ (reportErr . toElabError) errs
  fromJust' res

unquote :: MathParser QExpr
unquote = do
  single ','
  notFollowedBy $ satisfy (\c -> c == ' ' || c == '\n')
  lift $ QUnquote <$> lispVal

token1 :: MathParser (AtPos T.Text)
token1 = ReaderT $ \pe -> ParsecT $ \s@(State t o pst) cok _ _ eerr ->
  let
    go t' i = case T.uncons t' of
      Nothing -> eerr (TrivialError (o+i) (pure EndOfInput) mempty) s
      Just (c, t2) -> case delimVal (pDelims pe) c of
        0 -> go t2 (i+1)
        d | testBit d 0 ->
          cok (AtPos o (T.take (i+1) t)) (State t2 (o+i+1) pst) mempty
        d | testBit d 1 ->
          cok (AtPos o (T.take i t)) (State t' (o+i) pst) mempty
        4 | i == 0 ->
          eerr (TrivialError o (Just (Tokens (pure c))) mempty) s
        4 ->
          let (t1', t2') = T.span (\c -> c == '\n' || c == ' ') t2 in
          cok (AtPos o (T.take i t)) (State t2' (o+i+T.length t1') pst) mempty
  in go t 0

tkSatisfy :: (T.Text -> Bool) -> MathParser (AtPos T.Text)
tkSatisfy p = do
  at@(AtPos _ t) <- token1
  guard (p t)
  return at

tk :: T.Text -> MathParser ()
tk t = label (T.unpack t) $ () <$ tkSatisfy (== t)

checkPrec :: Prec -> Bool -> T.Text -> MathParser Prec
checkPrec p r v = do
  Just (_, q) <- asks (H.lookup v . pPrec)
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
  (tk "(" *> parseExpr 0 <* tk ")") <|>
  do {
    AtPos o v <- token1;
    (checkPrec p True v >> do
      PrefixInfo _ x lits <- asks (H.lookup v . pPrefixes) >>= fromMaybeM
      QApp (AtPos o x) <$> parseLiterals lits) <|>
    (guard (isIdent v) >>
      QApp (AtPos o v) <$>
        if p <= appPrec then many (parsePrefix maxBound) else return []) }

maybeLookahead :: MathParser a -> MathParser (a, MathParser ())
maybeLookahead p = lookAhead $
  liftM2 (,) p (updateParserState . const <$> getParserState)

getLhs :: Prec -> QExpr -> MathParser QExpr
getLhs p lhs =
  (do
    (AtPos o v, commit) <- maybeLookahead token1
    q <- checkPrec p True v
    InfixInfo _ x _ <- asks (H.lookup v . pInfixes) >>= fromMaybeM
    commit
    rhs <- parsePrefix p >>= getRhs q
    getLhs p (QApp (AtPos o x) [lhs, rhs])) <|>
  return lhs

getRhs :: Prec -> QExpr -> MathParser QExpr
getRhs p rhs =
  (do
    (AtPos o v, commit) <- maybeLookahead token1
    InfixInfo _ x r <- asks (H.lookup v . pInfixes) >>= fromMaybeM
    q <- checkPrec p r v
    commit
    getLhs q rhs >>= getRhs p) <|>
  return rhs

parseExpr :: Prec -> MathParser QExpr
parseExpr p = parsePrefix p >>= getLhs p
