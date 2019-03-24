-- | A simple plain text parser for the proof format.
-- Intended mainly for debugging.
module ProofTextParser(parseProof) where

import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Applicative
import Debug.Trace
import Text.ParserCombinators.ReadP hiding (get)
import qualified Text.Read.Lex as L
import qualified Data.Map.Strict as M
import AST
import ProofTypes

type NameMap = (Int, M.Map Ident Int)

nempty :: NameMap
nempty = (0, M.empty)

ninsert :: Ident -> NameMap -> NameMap
ninsert v (n, m) = (n+1, M.insert v n m)

data ParserState = ParserState {
  -- | Map from sort to SortID
  pSortIx :: NameMap,
  -- | Map from term to TermID
  pTermIx :: NameMap,
  -- | Map from theorem to ThmID
  pThmIx :: NameMap,
  -- | Map from var to VarID
  pVarIx :: NameMap }

type Parser = StateT ParserState ReadP

(<|+) :: Parser a -> Parser a -> Parser a
p <|+ q = StateT $ \s -> runStateT p s <++ runStateT q s

readlist :: Parser a -> Parser [a]
readlist p = go where go = ((:) <$> p <*> go) <|+ return []

parseProof :: String -> Maybe Proofs
parseProof s = let start = ParserState nempty nempty nempty nempty in
  case readP_to_S (evalStateT readProofs start <* L.expect L.EOF) s of
    ((c, _):_) -> Just c
    _ -> Nothing

readProofs :: Parser Proofs
readProofs = readlist readProof

lex1 :: Parser L.Lexeme
lex1 = lift L.lex

expect :: L.Lexeme -> Parser ()
expect = lift . L.expect

expectS :: String -> Parser ()
expectS = expect . L.Symbol

bracket :: String -> String -> Parser a -> Parser a
bracket l r a = expect (L.Punc l) *> a <* expect (L.Punc r)

insertSort :: Parser Ident
insertSort = StateT $ \s -> do
  L.Ident i <- L.lex
  return (i, s {pSortIx = ninsert i (pSortIx s)})

insertTerm :: Parser Ident
insertTerm = StateT $ \s -> do
  L.Ident i <- L.lex
  return (i, s {pTermIx = ninsert i (pTermIx s)})

insertVar :: Parser Ident
insertVar = StateT $ \s -> do
  L.Ident i <- L.lex
  return (i, s {pVarIx = ninsert i (pVarIx s)})

insertThm :: Parser Ident
insertThm = StateT $ \s -> do
  L.Ident i <- L.lex
  return (i, s {pThmIx = ninsert i (pThmIx s)})

lookupRead :: (ParserState -> NameMap) -> Parser Int
lookupRead f = do
  L.Ident i <- lex1
  s <- get
  maybe empty return (snd (f s) M.!? i)

readSort :: Parser SortID
readSort = SortID <$> lookupRead pSortIx

readTerm :: Parser TermID
readTerm = TermID <$> lookupRead pTermIx

readAssrt :: Parser ThmID
readAssrt = ThmID <$> lookupRead pThmIx

readVar :: Parser VarID
readVar = VarID <$> lookupRead pVarIx

resetVars :: Parser ()
resetVars = modify (\s -> s {pVarIx = (0, M.empty)})

readProof :: Parser ProofCmd
readProof = lex1 >>= \case
  L.Ident "sort" -> StepSort <$> insertSort
  L.Ident "term" -> StepTerm <$> insertTerm
  L.Ident "axiom" -> StepAxiom <$> insertThm
  L.Ident "def" -> readDef True
  L.Ident "theorem" -> readThm True
  L.Ident "local" -> lex1 >>= \case
    L.Ident "def" -> readDef False
    L.Ident "theorem" -> readThm False
  _ -> empty

readDef :: Bool -> Parser ProofCmd
readDef st = do
  trace "readDef" (return ())
  x <- insertTerm
  traceShow x (return ())
  args <- readlist readBinder
  traceShow args (return ())
  expectS ":"
  traceShow ":" (return ())
  ret <- VType <$> readSort <*> readlist readVar
  traceShow ret (return ())
  expect $ L.Punc "="
  ds <- readlist readDummy
  val <- readExpr
  resetVars >> return (ProofDef (Just x) args ret ds val st)

readThm :: Bool -> Parser ProofCmd
readThm st = do
  trace ("readThm " ++ show st) (return ())
  x <- insertThm
  traceShow x (return ())
  vs <- readlist readBinder
  traceShow vs (return ())
  expect (L.Punc ",")
  traceShow "," (return ())
  uf <- (do
      expect $ L.Ident "unfolding"
      t <- readTerm
      bracket "(" ")" (readlist insertVar)
      return (Just t))
    <|+ return Nothing
  traceShow uf (return ())
  ds <- readlist readDummy
  traceShow ds (return ())
  hyps <- readlist readHyp
  traceShow hyps (return ())
  expectS ":"
  traceShow ":" (return ())
  ret <- readExpr
  traceShow ret (return ())
  expect $ L.Punc "="
  traceShow "=" (return ())
  proof <- (\l -> l []) <$> readProofExpr
  traceShow proof (return ())
  resetVars >> return (ProofThm (Just x) vs hyps ret uf ds proof st)

readDummy :: Parser SortID
readDummy = bracket "{" "}" (insertVar >> expectS ":" >> readSort)

readBinder :: Parser VBinder
readBinder = (VBound <$> readDummy) <|+
  bracket "(" ")" (insertVar >> expectS ":" >>
    VReg <$> readSort <*> readlist readVar)

readExpr :: Parser VExpr
readExpr = (VVar <$> readVar) <|+ (flip VApp [] <$> readTerm) <|+
  (bracket "(" ")" (VApp <$> readTerm <*> readlist readExpr))

readHyp :: Parser VExpr
readHyp = bracket "(" ")" (insertVar >> expectS ":" >> readExpr)

exprToLocal :: VExpr -> [LocalCmd] -> [LocalCmd]
exprToLocal (VVar (VarID v)) r = Load v : r
exprToLocal (VApp t es) r = foldr exprToLocal (PushApp t : r) es

readProofExpr :: Parser ([LocalCmd] -> [LocalCmd])
readProofExpr =
  (expectS "?" >> return (Sorry :)) <|+
  (exprToLocal <$> readExpr) <|+
  bracket "(" ")" (do
    t <- readAssrt
    es <- readlist readExpr
    hs <- readlist readProofExpr
    return (\r -> foldr exprToLocal (foldr ($) (PushThm t : r) hs) es)) <|+
  bracket "[" "]" (do
    trace "[" (return ())
    e <- readProofExpr
    traceShow (e[]) (return ())
    expect (L.Punc "=")
    trace "=" (return ())
    insertVar
    trace "var" (return ())
    return (e . (Save :)))
