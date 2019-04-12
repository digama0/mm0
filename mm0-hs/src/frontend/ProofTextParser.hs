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
import Environment (Ident)
import ProofTypes

type Parser = StateT IxLookup ReadP

(<|+) :: Parser a -> Parser a -> Parser a
p <|+ q = StateT $ \s -> runStateT p s <++ runStateT q s

readlist :: Parser a -> Parser [a]
readlist p = go where go = ((:) <$> p <*> go) <|+ return []

parseProof :: String -> Maybe Proofs
parseProof s =
  case readP_to_S (evalStateT readProofs mkIxLookup <* L.expect L.EOF) s of
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
  return (i, ilInsertSort i s)

insertTerm :: Parser Ident
insertTerm = StateT $ \s -> do
  L.Ident i <- L.lex
  return (i, ilInsertTerm i s)

insertVar :: Parser Ident
insertVar = StateT $ \s -> do
  L.Ident i <- L.lex
  return (i, ilInsertVar i s)

insertThm :: Parser Ident
insertThm = StateT $ \s -> do
  L.Ident i <- L.lex
  return (i, ilInsertThm i s)

lookupRead :: (IxLookup -> NameMap) -> Parser Int
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
resetVars = modify ilResetVars

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
  L.Ident "input" -> lex1 >>= \case
    L.Ident "string" -> return $ StepInout (VIKString False)
    _ -> empty
  L.Ident "output" -> lex1 >>= \case
    L.Ident "string" -> return $ StepInout (VIKString True)
    _ -> empty
  _ -> empty

readDef :: Bool -> Parser ProofCmd
readDef st = do
  x <- insertTerm
  args <- readlist readBinder
  expectS ":"
  ret <- VType <$> readSort <*> readlist readVar
  expect $ L.Punc "="
  ds <- readlist readDummy
  val <- readExpr
  resetVars >> return (ProofDef (Just x) args ret ds val st)

readThm :: Bool -> Parser ProofCmd
readThm st = do
  trace ("readThm " ++ show st) (return ())
  x <- insertThm
  vs <- readlist readBinder
  expect (L.Punc ",")
  uf <- (do
      expect $ L.Ident "unfolding"
      t <- readlist readTerm
      bracket "(" ")" (readlist insertVar)
      return t)
    <|+ return []
  ds <- readlist readDummy
  hyps <- readlist readHyp
  expectS ":"
  ret <- readExpr
  expect $ L.Punc "="
  proof <- (\l -> l []) <$> readProofExpr
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
