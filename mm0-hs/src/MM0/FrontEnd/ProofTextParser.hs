-- | A simple plain text parser for the proof format.
-- Intended mainly for debugging.
module MM0.FrontEnd.ProofTextParser (parseProof) where

import Control.Applicative hiding (many, (<|>))
import Control.Monad
import Data.Word8
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Byte
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString.Lazy.Char8 as BC
import qualified Data.Text as T
import qualified Data.Vector as V
import MM0.Kernel.Environment
import MM0.Kernel.Types
import MM0.Util

type Parser = Parsec Void B.ByteString

parseProof :: B.ByteString -> Either String [Stmt]
parseProof s = case runParser (space *> many readLisp <* eof) "" s of
  Left err -> Left (show err)
  Right c -> mapM readStmt c

data Lisp = Atom T.Text | List [Lisp] deriving (Show)

symbol :: Word8 -> Parser ()
symbol c = char c >> space

paren :: Parser a -> Parser a
paren = between (symbol _parenleft) (symbol _parenright)

lispIdentV :: V.Vector Bool
lispIdentV = V.generate 256 (f . fromIntegral) where
  f c = isAlphaNum c || toChar c `elem` ("!%&*/:<=>?^_~+-.@" :: String)

lispIdent :: Word8 -> Bool
lispIdent = (lispIdentV V.!) . fromIntegral where

ident :: Parser Ident
ident = do
  s <- takeWhileP (Just "identifier char") lispIdent
  guard (not (BC.null s))
  T.pack (BC.unpack s) <$ space

readLisp :: Parser Lisp
readLisp = paren (List <$> many readLisp) <|> (Atom <$> ident)

readStmt :: Lisp -> Either String Stmt
readStmt (List [Atom "sort", Atom x]) = return (StepSort x)
readStmt (List [Atom "term", Atom x]) = return (StepTerm x)
readStmt (List [Atom "axiom", Atom x]) = return (StepAxiom x)
readStmt (List (Atom "def" : es)) = readDef True es
readStmt (List (Atom "pub" : Atom "def" : es)) = readDef True es
readStmt (List (Atom "local" : Atom "def" : es)) = readDef False es
readStmt (List (Atom "theorem" : es)) = readThm True es
readStmt (List (Atom "pub" : Atom "theorem" : es)) = readThm True es
readStmt (List (Atom "local" : Atom "theorem" : es)) = readThm False es
readStmt (List [Atom "input", Atom "string"]) = return $ StepInout (VIKString False)
readStmt (List [Atom "output", Atom "string"]) = return $ StepInout (VIKString True)
readStmt l = Left $ "invalid command " ++ show l

readDef :: Bool -> [Lisp] -> Either String Stmt
readDef st [Atom x, List bis, List ret, List ds, val] = do
  bis' <- mapM readBinder bis
  ret' <- readDepType ret
  ds' <- mapM readBound ds
  val' <- readSExpr val
  return $ StmtDef x bis' ret' ds' val' st
readDef _ l = Left $ "invalid def " ++ show l

readThm :: Bool -> [Lisp] -> Either String Stmt
readThm st [Atom x, List bis, List hs, ret, List ds, pf] = do
  bis' <- mapM readBinder bis
  hs' <- mapM readHyp hs
  ret' <- readSExpr ret
  ds' <- mapM readBound ds
  pf' <- readProof pf
  return $ StmtThm x bis' hs' ret' ds' pf' st
readThm _ l = Left $ "invalid theorem " ++ show l

readAtom :: Lisp -> Either String Ident
readAtom (Atom x) = return x
readAtom e = Left $ "invalid variable " ++ show e

readDepType :: [Lisp] -> Either String DepType
readDepType [Atom s, List vs] = DepType s <$> mapM readAtom vs
readDepType l = Left $ "invalid type " ++ show l

readBound :: Lisp -> Either String (VarName, Sort)
readBound (List [Atom x, Atom s]) = return (x, s)
readBound l = Left $ "invalid dummy declaration " ++ show l

readBinder :: Lisp -> Either String PBinder
readBinder (List [Atom x, Atom s]) = return $ PBound x s
readBinder (List (Atom x : es)) = PReg x <$> readDepType es
readBinder l = Left $ "invalid binder " ++ show l

readSExpr :: Lisp -> Either String SExpr
readSExpr (Atom x) = return $ SVar x
readSExpr (List (Atom t : es)) = App t <$> mapM readSExpr es
readSExpr e = Left $ "invalid s-expr " ++ show e

readHyp :: Lisp -> Either String (VarName, SExpr)
readHyp (List [Atom x, e]) = (x,) <$> readSExpr e
readHyp l = Left $ "invalid hypothesis " ++ show l

readProof :: Lisp -> Either String Proof
readProof (Atom "?") = return PSorry
readProof (Atom x) = return $ PHyp x
readProof (List (Atom ":conv" : es)) = case es of
  [e, c, p] -> liftA3 PConv (readSExpr e) (readConv c) (readProof p)
  _ -> Left $ "invalid :conv " ++ show es
readProof (List (Atom ":let" : es)) = case es of
  [Atom x, p1, p2] -> liftA2 (PLet x) (readProof p1) (readProof p2)
  _ -> Left $ "invalid :let " ++ show es
readProof (List (Atom t : List es : ps)) =
  liftA2 (PThm t) (mapM readSExpr es) (mapM readProof ps)
readProof l = Left $ "invalid hypothesis " ++ show l

readConv :: Lisp -> Either String Conv
readConv (Atom x) = return $ CVar x
readConv (List (Atom ":sym" : es)) = case es of
  [c] -> CSym <$> readConv c
  _ -> Left $ "invalid :sym " ++ show es
readConv (List (Atom ":unfold" : es)) = case es of
  [Atom t, List es', List vs, c] ->
    liftA3 (CUnfold t) (mapM readSExpr es') (mapM readAtom vs) (readConv c)
  _ -> Left $ "invalid :unfold " ++ show es
readConv (List (Atom t : es)) = CApp t <$> mapM readConv es
readConv e = Left $ "invalid conv " ++ show e
