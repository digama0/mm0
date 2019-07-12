-- | A simple plain text parser for the proof format.
-- Intended mainly for debugging.
module ProofTextParser(parseProof) where

import Control.Applicative hiding (many, (<|>))
import Data.Word8
import Data.Void
import Data.Default
import Text.Megaparsec
import Text.Megaparsec.Byte
import Control.Monad.Trans.State
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString.Lazy.Char8 as BC
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Environment (Ident)
import ProofTypes
import Util

type Parser = StateT IxLookup (Parsec Void B.ByteString)

parseProof :: B.ByteString -> Either String Proofs
parseProof s = case runParser (evalStateT readProofs def) "" s of
  Left err -> Left (show err)
  Right c -> Right c

readProofs :: Parser Proofs
readProofs = space *> many readProof <* eof

str :: String -> Parser ()
str s = () <$ string (BC.pack s)

symbol :: Word8 -> Parser ()
symbol c = char c >> space

bracket :: Word8 -> Word8 -> Parser a -> Parser a
bracket l r = between (symbol l) (symbol r)

paren :: Parser a -> Parser a
paren = bracket _parenleft _parenright

identStart :: Word8 -> Bool
identStart c = isAlpha c || c == _underscore

identRest :: Word8 -> Bool
identRest c = isAlphaNum c || c == _underscore

ident :: Parser Ident
ident = T.pack <$> liftA2 (:) (toChar <$> satisfy identStart)
  (BC.unpack <$> takeWhileP (Just "identifier char") identRest) <* space

insertSort :: Parser Ident
insertSort = do
  i <- ident
  modify (ilInsertSort i)
  return i

insertTerm :: Parser Ident
insertTerm = do
  i <- ident
  modify (ilInsertTerm i)
  return i

insertVar :: Parser Ident
insertVar = do
  i <- ident
  modify (ilInsertVar i)
  return i

insertThm :: Parser Ident
insertThm = do
  i <- ident
  modify (ilInsertThm i)
  return i

lookupRead :: (IxLookup -> NameMap) -> Parser Int
lookupRead f = do
  s <- get
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
resetVars = modify ilResetVars

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
    _ -> empty
  "input" -> ident >>= \case
    "string" -> return $ StepInout (VIKString False)
    _ -> empty
  "output" -> ident >>= \case
    "string" -> return $ StepInout (VIKString True)
    _ -> empty
  _ -> empty

readDef :: Bool -> Parser ProofCmd
readDef st = do
  x <- insertTerm
  args <- many readBinder
  symbol _colon
  ret <- liftA2 VType readSort (many (readVar <?> "var"))
  symbol _equal
  ds <- many readDummy
  val <- readExpr
  resetVars >> return (ProofDef (Just x) args ret ds val st)

readThm :: Bool -> Parser ProofCmd
readThm st = do
  x <- insertThm
  vs <- many readBinder
  symbol _comma
  uf <- (do
      str "unfolding" <* space
      t <- many readTerm
      _ <- paren (many insertVar)
      return t)
    <|> return []
  hyps <- many readHyp
  symbol _colon
  ret <- readExpr
  symbol _equal
  ds <- many readDummy
  proof <- readProofExpr
  resetVars >> return (ProofThm (Just x) vs hyps ret uf ds proof st)

readDummy :: Parser SortID
readDummy = bracket _braceleft _braceright
  (insertVar >> symbol _colon >> readSort)

readBinder :: Parser VBinder
readBinder = (VBound <$> readDummy) <|>
  paren (insertVar >> symbol _colon >>
    VReg <$> readSort <*> many readVar)

readExpr :: Parser VExpr
readExpr = (VVar <$> try readVar) <|> (flip VApp [] <$> readTerm) <|>
  (paren (VApp <$> readTerm <*> many readExpr))

readHyp :: Parser VExpr
readHyp = paren (insertVar >> symbol _colon >> readExpr)

readProofExpr :: Parser ProofTree
readProofExpr =
  (symbol _question >> return Sorry) <|>
  paren (
    (do
      t <- try readTerm
      es <- many readProofExpr
      return (VTerm t es)) <|>
    (do
      t <- readAssrt
      hs <- many readProofExpr
      return (VThm t hs))) <|>
  bracket _bracketleft _bracketright (do
    e <- readProofExpr
    symbol _equal
    _ <- insertVar
    return (Save e)) <|>
  (Load <$> try readVar) <|>
  (flip VTerm [] <$> try readTerm) <|>
  (flip VThm [] <$> readAssrt)
