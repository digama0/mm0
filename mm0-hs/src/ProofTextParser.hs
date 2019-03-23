-- | A simple plain text parser for the proof format.
-- Intended mainly for debugging.
module ProofTextParser(parseProof) where

import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Applicative
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
readlist p = go where go = (p >> go) <|+ return []

parseProof :: String -> Maybe Proofs
parseProof s = let start = ParserState nempty nempty nempty nempty in
  case readP_to_S (evalStateT readProofs start <* eof) s of
    ((c, _):_) -> Just c
    _ -> Nothing

readProofs :: Parser Proofs
readProofs = readlist readProof

lex1 :: Parser L.Lexeme
lex1 = lift L.lex

expect :: String -> Parser ()
expect = lift . L.expect . L.Symbol

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
  L.Ident "def" -> insertTerm >>= readDef . Just
  L.Ident "theorem" -> insertThm >>= readThm . Just
  L.Ident "local" -> lex1 >>= \case
    L.Ident "def" -> insertTerm >> readDef Nothing
    L.Ident "theorem" -> insertThm >> readThm Nothing
  _ -> empty

readDef :: Maybe Ident -> Parser ProofCmd
readDef st = do
  args <- readlist readBinder
  expect ":"
  ret <- VType <$> readSort <*> readlist readVar
  expect "="
  ds <- readlist readDummy
  val <- readExpr
  resetVars >> return (ProofDef args ret ds val st)

readThm :: Maybe Ident -> Parser ProofCmd
readThm st = do
  vs <- readlist readBinder
  expect ","
  uf <- (do
      expect "unfolding"
      t <- readTerm
      expect "(" >> readlist insertVar >> expect ")"
      return (Just t))
    <|+ return Nothing
  ds <- readlist readDummy
  hyps <- readlist readHyp
  ret <- readExpr
  proof <- readProofExpr
  resetVars >> return (ProofThm vs hyps ret uf ds proof st)

readBinder :: Parser VBinder
readBinder = lex1 >>= \case
  L.Symbol "(" -> insertVar >> expect ":" >>
    VReg <$> readSort <*> readlist readVar <* expect ")"
  L.Symbol "{" -> insertVar >> expect ":" >>
    VBound <$> readSort <* expect "}"
  _ -> empty

readDummy :: Parser SortID
readDummy = readBinder >>= \case
  VBound s -> return s
  _ -> empty

readExpr :: Parser VExpr
readExpr = (VVar <$> readVar) <|+ (flip VApp [] <$> readTerm) <|+
  (expect "(" *> (VApp <$> readTerm <*> readlist readExpr) <* expect ")")

readHyp :: Parser VExpr
readHyp = expect "(" >> insertVar >> expect ":" >> readExpr <* expect ")"

readProofExpr :: Parser [LocalCmd]
readProofExpr = (do
    expect "let"
    insertVar
    expect "="
    es <- readSimpleExpr
    r <- readProofExpr
    return (es (Save : r)))
  <|+ ((\l -> l []) <$> readSimpleExpr)

exprToLocal :: VExpr -> [LocalCmd] -> [LocalCmd]
exprToLocal (VVar (VarID v)) r = Load v : r
exprToLocal (VApp t es) r = foldr exprToLocal (PushApp t : r) es

readSimpleExpr :: Parser ([LocalCmd] -> [LocalCmd])
readSimpleExpr = (exprToLocal <$> readExpr) <|+
  (expect "(" *> (do
    t <- readAssrt
    es <- readlist readExpr
    hs <- readlist readSimpleExpr
    return (\r -> foldr exprToLocal (foldr ($) (PushThm t : r) hs) es))
  <* expect ")")
