-- | A simple plain text parser for the proof format.
-- Intended mainly for debugging.
module MM0.FrontEnd.ProofTextParser (parseProof) where

import Control.Applicative hiding (many, (<|>))
import Data.Word8
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Byte
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString.Lazy.Char8 as BC
import qualified Data.Text as T
import MM0.Kernel.Environment
import MM0.Kernel.Types
import MM0.Util

type Parser = Parsec Void B.ByteString

parseProof :: B.ByteString -> Either String [Stmt]
parseProof s = case runParser readStmts "" s of
  Left err -> Left (show err)
  Right c -> Right c

readStmts :: Parser [Stmt]
readStmts = space *> many readStmt <* eof

_str :: String -> Parser ()
_str s = () <$ string (BC.pack s)

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

readSort :: Parser Sort
readSort = ident <?> "lookup sort"

readTerm :: Parser TermName
readTerm = ident <?> "lookup term"

readAssrt :: Parser ThmName
readAssrt = ident <?> "lookup thm"

readVar :: Parser VarName
readVar = ident <?> "lookup var"

readStmt :: Parser Stmt
readStmt = ident >>= \case
  "sort" -> StepSort <$> readSort
  "term" -> StepTerm <$> readTerm
  "axiom" -> StepAxiom <$> readAssrt
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

readDef :: Bool -> Parser Stmt
readDef st = do
  x <- readTerm
  args <- many readBinder
  symbol _colon
  ret <- liftA2 DepType readSort (many (readVar <?> "var"))
  symbol _equal
  ds <- many (readBound (,))
  val <- readExpr
  return $ StmtDef x args ret ds val st

readThm :: Bool -> Parser Stmt
readThm st = do
  x <- readAssrt
  vs <- many readBinder
  symbol _comma
  hyps <- many readHyp
  symbol _colon
  ret <- readExpr
  symbol _equal
  ds <- many (readBound (,))
  proof <- readProof
  return $ StmtThm x vs hyps ret ds proof st

readBound :: (VarName -> Sort -> a) -> Parser a
readBound f = bracket _braceleft _braceright
  (liftA2 f ident (symbol _colon >> readSort))

readBinder :: Parser PBinder
readBinder = (readBound PBound) <|>
  paren (liftA2 PReg ident $
    symbol _colon >> liftA2 DepType readSort (many readVar))

readExpr :: Parser SExpr
readExpr = (SVar <$> try ident) <|> (paren (liftA2 App readTerm (many readExpr)))

readHyp :: Parser (VarName, SExpr)
readHyp = paren (liftA2 (,) ident $ symbol _colon >> readExpr)

readProof :: Parser Proof
readProof = error "unimplemented" -- TODO
  -- (symbol _question >> return Sorry) <|>
  -- paren (
  --   (do
  --     t <- try readTerm
  --     es <- many readProof
  --     return (App t es)) <|>
  --   (do
  --     t <- readAssrt
  --     hs <- many readProof
  --     return (VThm t hs))) <|>
  -- bracket _bracketleft _bracketright (do
  --   e <- readProof
  --   symbol _equal
  --   _ <- insertVar
  --   return (Save e)) <|>
  -- (Load <$> try readVar) <|>
  -- (flip VTerm [] <$> try readTerm) <|>
  -- (flip VThm [] <$> readAssrt)
