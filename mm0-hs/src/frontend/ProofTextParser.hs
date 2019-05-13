-- | A simple plain text parser for the proof format.
-- Intended mainly for debugging.
module ProofTextParser(parseProof) where

import Control.Applicative hiding (many, (<|>))
import Data.Char
import Debug.Trace
import Text.Parsec
import Text.Parsec.Char
import qualified Data.ByteString.Lazy as B
import qualified Data.Map.Strict as M
import Environment (Ident)
import ProofTypes

type Parser = Parsec B.ByteString IxLookup

parseProof :: B.ByteString -> Either String Proofs
parseProof s = case runParser readProofs mkIxLookup "" s of
  Left err -> Left (show err)
  Right c -> Right c

readProofs :: Parser Proofs
readProofs = spaces *> many readProof <* eof

symbol :: Char -> Parser ()
symbol c = char c >> spaces

bracket :: Char -> Char -> Parser a -> Parser a
bracket l r = between (symbol l) (symbol r)

identStart :: Char -> Bool
identStart c = isAlpha c || c == '_'

identRest :: Char -> Bool
identRest c = isAlphaNum c || c == '_'

ident :: Parser Ident
ident = liftA2 (:) (satisfy identStart) (many (satisfy identRest)) <* spaces

insertSort :: Parser Ident
insertSort = do
  i <- ident
  modifyState (ilInsertSort i)
  return i

insertTerm :: Parser Ident
insertTerm = do
  i <- ident
  modifyState (ilInsertTerm i)
  return i

insertVar :: Parser Ident
insertVar = do
  i <- ident
  modifyState (ilInsertVar i)
  return i

insertThm :: Parser Ident
insertThm = do
  i <- ident
  modifyState (ilInsertThm i)
  return i

lookupRead :: (IxLookup -> NameMap) -> Parser Int
lookupRead f = do
  s <- getState
  i <- ident
  maybe empty return (snd (f s) M.!? i)

readSort :: Parser SortID
readSort = SortID <$> lookupRead pSortIx <?> "lookup sort"

readTerm :: Parser TermID
readTerm = TermID <$> lookupRead pTermIx <?> "lookup term"

readAssrt :: Parser ThmID
readAssrt = ThmID <$> lookupRead pThmIx <?> "lookup thm"

readVar :: Parser VarID
readVar = VarID <$> lookupRead pVarIx <?> "lookup var"

resetVars :: Parser ()
resetVars = modifyState ilResetVars

readProof :: Parser ProofCmd
readProof = ident >>= \case
  "sort" -> StepSort <$> insertSort
  "term" -> StepTerm <$> insertTerm
  "axiom" -> StepAxiom <$> insertThm
  "def" -> readDef True
  "theorem" -> readThm True
  "local" -> ident >>= \case
    "def" -> readDef False
    "theorem" -> readThm False
  "input" -> ident >>= \case
    "string" -> return $ StepInout (VIKString False)
    _ -> empty
  "output" -> ident >>= \case
    "string" -> return $ StepInout (VIKString True)
    _ -> empty
  l -> empty

readDef :: Bool -> Parser ProofCmd
readDef st = do
  x <- insertTerm
  args <- many readBinder
  symbol ':'
  ret <- liftA2 VType readSort (many (readVar <?> "var"))
  symbol '='
  ds <- many readDummy
  val <- readExpr
  resetVars >> return (ProofDef (Just x) args ret ds val st)

readThm :: Bool -> Parser ProofCmd
readThm st = do
  x <- insertThm
  vs <- many readBinder
  symbol ','
  uf <- (do
      string "unfolding" <* spaces
      t <- many readTerm
      bracket '(' ')' (many insertVar)
      return t)
    <|> return []
  hyps <- many readHyp
  symbol ':'
  ret <- readExpr
  symbol '='
  ds <- many readDummy
  proof <- readProofExpr
  resetVars >> return (ProofThm (Just x) vs hyps ret uf ds proof st)

readDummy :: Parser SortID
readDummy = bracket '{' '}' (insertVar >> symbol ':' >> readSort)

readBinder :: Parser VBinder
readBinder = (VBound <$> readDummy) <|>
  bracket '(' ')' (insertVar >> symbol ':' >>
    VReg <$> readSort <*> many readVar)

readExpr :: Parser VExpr
readExpr = (VVar <$> try readVar) <|> (flip VApp [] <$> readTerm) <|>
  (bracket '(' ')' (VApp <$> readTerm <*> many readExpr))

readHyp :: Parser VExpr
readHyp = bracket '(' ')' (insertVar >> symbol ':' >> readExpr)

readProofExpr :: Parser ProofTree
readProofExpr =
  (symbol '?' >> return Sorry) <|>
  bracket '(' ')' (
    (do
      t <- try readTerm
      es <- many readProofExpr
      return (VTerm t es)) <|>
    (do
      t <- readAssrt
      hs <- many readProofExpr
      return (VThm t hs))) <|>
  bracket '[' ']' (do
    e <- readProofExpr
    symbol '='
    insertVar
    return (Save e)) <|>
  (Load <$> try readVar) <|>
  (flip VTerm [] <$> try readTerm) <|>
  (flip VThm [] <$> readAssrt)
