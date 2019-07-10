{-# LANGUAGE BangPatterns #-}
module CMathParser (parseFormula, parseFormulaProv) where

import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Class
import Data.Void
import qualified Data.HashMap.Strict as H
import qualified Data.List.NonEmpty as NE
import qualified Data.IntMap as I
import qualified Data.Vector as V
import qualified Data.Text as T
import CAST
import CEnv
import CParser (Parser, initialPosState)
import MathParser (appPrec)
import Util

data Tokens = Eof Offset
  | Token (Span Token) Tokens -- token
  | Unquote (Span LispVal) Tokens -- unquote

tokenOffset :: Tokens -> Offset
tokenOffset (Eof o) = o
tokenOffset (Token (Span o _ _) _) = o
tokenOffset (Unquote (Span o _ _) _) = o

tokenize :: Delims -> Formula -> Tokens
tokenize delims (Formula o t) = space o t where

  space :: Offset -> T.Text -> Tokens
  space !o t =
    let (t1, t2) = T.span (\c -> c == '\n' || c == ' ') t in
    token (o + T.length t1) t2

  token :: Offset -> T.Text -> Tokens
  token !o t =
    let (t1, t2) = T.span ((== 0) . delimVal delims) t in
    if T.null t2 then
      if T.null t1 then Eof o
      else let o' = o + T.length t1 in Token (Span o t1 o') $ token o' t2
    else case delimVal delims (T.head t2) of
      -- | left delimiter
      1 -> let {n = T.length t1 + 1; (t1, t2) = T.splitAt n t} in
           Token (Span o t1 (o+n)) $ token (o+n) t2
      -- | right delimiter
      2 -> let o' = o + T.length t1 in Token (Span o t1 o') $ token o' t2
      -- | both delimiter
      3 -> let o' = o + T.length t1 in Token (Span o t1 o') $
           let (t2', t3) = T.splitAt 1 t2 in Token (Span o' t2' (o'+1)) $
           token (o'+1) t3
      -- | space
      4 -> let o' = o + T.length t1 in Token (Span o t1 o') $ space o' t

type MParser = StateT Tokens ElabM

ofParser :: Parser a -> MParser a
ofParser p = undefined

parseFormula :: T.Text -> Maybe Sort -> Formula -> ElabM (Span LispVal, Sort)
parseFormula thm tgt fmla = do
  delims <- gets (pDelims . ePE)
  runStateT (parseExpr tgt 0) (tokenize delims fmla) >>= \case
    (v, Eof _) -> return v
    (_, tks) -> escapeAt (tokenOffset tks) "math parse error: expected '$'"

parseFormulaProv :: T.Text -> Formula -> ElabM (Span LispVal, Sort)
parseFormulaProv thm fmla = do
  gets eProvableSorts >>= \case
    [tgt] -> parseFormula thm (Just tgt) fmla
    _ -> do
      (Span o1 sexp o2, s) <- parseFormula thm Nothing fmla
      try (getCoeProv s) >>= \case
        Just (s2, c) -> return (Span o1 (c sexp) o2, s2)
        Nothing -> do
          reportErr $ ElabError ELError o1 o2
            ("type error, expected provable sort, got " <> s) []
          mzero

getOffset :: MParser Offset
getOffset = gets tokenOffset

parseError :: T.Text -> MParser a
parseError msg = getOffset >>= lift . flip escapeAt msg

coerce :: Sort -> (Span LispVal, Sort) -> MParser (Span LispVal)
coerce s2 (Span o1 sexp o2, s1) =
  lift $ try (getCoe s1 s2) >>= \case
    Just c -> return (Span o1 (c sexp) o2)
    Nothing -> do
      reportErr $ ElabError ELError o1 o2
        ("type error, expected " <> s2 <> ", got " <> s1) []
      mzero

{-
tkMatch :: (Token -> Maybe b) -> (Span Token -> b -> MParser a) -> MParser a -> MParser a
tkMatch f yes no = StateT $ \case
  Token t ss -> case f t of
    Nothing -> runStateT no (t : ss)
    Just b -> runStateT (yes t b) ss
  ss -> runStateT no ss

tkCond :: (T.Text -> Bool) -> MParser a -> MParser a -> MParser a
tkCond p yes no = tkMatch (\t -> if p t then Just () else Nothing) (\_ _ -> yes) no

tk :: T.Text -> MParser ()
tk t = tkCond (== t) (return ()) (parseError ("expected '" ++ t ++ "'"))

parseVar :: MParser (Span LispVal, Sort) -> MParser (Span LispVal, Sort)
parseVar no = do
  ctx <- ask
  tkMatch (lookupOrInferLocal ctx) (\v (DepType s _) -> return (SVar v, s)) no

parseLiteral :: MParser (Span LispVal, Sort) -> MParser (Span LispVal, Sort)
parseLiteral no =
  tkCond (== "(") (parseExpr 0 <* tk ")") (parseVar no)

checkPrec :: MParserEnv -> Prec -> T.Text -> Maybe a -> Maybe a
checkPrec e p v m = do
  (_, q) <- H.lookup v (pPrec e)
  if q >= p then m else Nothing

parseLiterals :: V.Vector T.Text -> [PLiteral] -> MParser [Span LispVal]
parseLiterals ls = go I.empty where
  go :: I.IntMap (Span LispVal) -> [PLiteral] -> MParser [Span LispVal]
  go m [] = return (I.elems m)
  go m (PConst t : lits) = tk t >> go m lits
  go m (PVar n p : lits) = do
    e <- parseExpr p >>= coerce (ls V.! n)
    go (I.insert n e m) lits

parsePrefix :: Maybe Sort -> Prec -> MParser (Span LispVal, Sort)
parsePrefix tgt p = parseLiteral $ do
  pe <- gets ePE
  tkMatch (\v -> checkPrec pe p v (H.lookup v (pPrefixes pe)))
    (\v (PrefixInfo _ x lits) -> do
      (_, bs, r) <- now >>= getTerm x
      let bss = V.fromList (dSort . binderType <$> bs)
      ss <- parseLiterals bss lits
      return (App x ss, dSort r)) $
    tkMatch (\v -> do
        d <- getTerm v
        if p <= appPrec || null (fst d) then Just d else Nothing)
      (\x (bs, r) -> do
        let bss = dSort . binderType <$> bs
        ss <- mapM (\s -> parsePrefix maxBound >>= coerce s) bss
        return (App x ss, dSort r)) $
    parseError "expected variable or prefix or term s-expr"

getLhs :: Prec -> (Span LispVal, Sort) -> MParser (Span LispVal, Sort)
getLhs p lhs = do
  pe <- gets ePE
  tkMatch (\v -> do
      q <- H.lookup v (pPrec pe)
      if q >= p then (,) q <$> H.lookup v (pInfixes pe) else Nothing)
    (\v (q, InfixInfo _ x _) -> do
      rhs <- parsePrefix p >>= getRhs q
      (_, [Binder _ _ (Just (DepType s1 _)),
           Binder _ _ (Just (DepType s2 _))], r) <- now >>= getTerm x
      Span o1 lhs' _ <- coerce s1 lhs
      Span _ rhs' o2 <- coerce s2 rhs
      getLhs p (Span o1 (List [Atom x, lhs', rhs']) o2, dSort r))
    (return lhs)

getRhs :: Prec -> (Span LispVal, Sort) -> MParser (Span LispVal, Sort)
getRhs p rhs = do
  pe <- gets ePE
  tkMatch (\v -> do
      (_, q) <- H.lookup v (pPrec pe)
      InfixInfo _ x r <- H.lookup v (pInfixes pe)
      if (if r then q >= p else q > p) then Just (q, x) else Nothing)
    (\v (q, x) -> modify (v:) >> getLhs q rhs >>= getRhs p)
    (return rhs)
-}

parseExpr :: Maybe Sort -> Prec -> MParser (Span LispVal, Sort)
parseExpr tgt p = undefined -- parsePrefix tgt p >>= getLhs p
