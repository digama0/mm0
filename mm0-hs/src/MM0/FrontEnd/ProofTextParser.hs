-- | A simple plain text parser for the proof format.
-- Intended mainly for debugging.
module MM0.FrontEnd.ProofTextParser (parseProof, parseProofOrDie) where

import Control.Applicative hiding (many, (<|>))
import Control.Monad.Trans.Class
import Control.Monad.State
import Control.Monad.Writer
import Data.Word8
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Byte
import qualified Data.ByteString as B
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Vector as V
import MM0.Kernel.Environment
import MM0.Kernel.Types
import MM0.Util

type ParserT = ParsecT Void B.ByteString

-- NOTE: because parsing generates large intermediate data structures,
-- it is important that it be processed lazily, and the obvious
-- Either String [Stmt] interface here would cause a space leak.
-- parseProofOrDie is the "pure" version, that exits the program on error,
-- and parseProof is the monadic version, that allows actions to trigger
-- when an error is encountered or a single statement is parsed.
parseProofOrDie :: B.ByteString -> [WCStmt]
parseProofOrDie s = f [] where
  (_, Endo f) = runWriter $ parseProof s error (tell . Endo . (:))

parseProof :: Monad m => B.ByteString -> (String -> m ()) -> (WCStmt -> m ()) -> m ()
parseProof s ferr fstmt =
  runParserT parseStmts "" s >>= \case
    Left err -> ferr (show err)
    Right () -> return ()
  where
  parseStmts = try (do
    c <- docComment
    l <- readLisp
    lift $ either ferr (fstmt . WC c) $ readStmt l
    parseStmts) <|> (ws >> eof)

data Lisp = Atom T.Text | List [Lisp] deriving (Show)

fromChar :: Char -> Word8
fromChar = toEnum . fromEnum

docComment :: Monad m => ParserT m Comment
docComment = do
  space
  s <- many (string "--|" *>
    takeWhileP (Just "non-newline") (/= fromChar '\n') <* char (fromChar '\n'))
  ws
  pure $ if null s then Nothing else Just $
    T.intercalate "\n" $ map (T.strip . T.decodeUtf8) s

ws :: Monad m => ParserT m ()
ws = do
  space
  try (do
    _ <- string "--" >> notFollowedBy (char $ fromChar '|')
    _ <- takeWhileP (Just "non-newline") (/= fromChar '\n')
    _ <- char (fromChar '\n')
    ws) <|> pure ()

symbol :: Monad m => Word8 -> ParserT m ()
symbol c = char c >> ws

paren :: Monad m => ParserT m a -> ParserT m a
paren = between (symbol _parenleft) (symbol _parenright)

lispIdentV :: V.Vector Bool
lispIdentV = V.generate 256 (f . fromIntegral) where
  f c = isAlphaNum c || toChar c `elem` ("!%&*/:<=>?^_~+-.@" :: String)

lispIdent :: Word8 -> Bool
lispIdent = (lispIdentV V.!) . fromIntegral

ident :: Monad m => ParserT m T.Text
ident = do
  s <- takeWhileP (Just "identifier char") lispIdent <* ws
  guard (not (B.null s))
  return $ T.decodeLatin1 s

readLisp :: Monad m => ParserT m Lisp
readLisp = paren (List <$> many readLisp) <|> (Atom <$> ident)

readStmt :: Lisp -> Either String Stmt
readStmt (List (Atom "sort" : Atom x : es)) = StmtSort x <$> readSortData es
readStmt (List (Atom "term" : es)) = readTerm es
readStmt (List (Atom "axiom" : es)) = readAxiom es
readStmt (List (Atom "def" : es)) = readDef True es
readStmt (List (Atom "pub" : Atom "def" : es)) = readDef True es
readStmt (List (Atom "local" : Atom "def" : es)) = readDef False es
readStmt (List (Atom "theorem" : es)) = readThm True es
readStmt (List (Atom "pub" : Atom "theorem" : es)) = readThm True es
readStmt (List (Atom "local" : Atom "theorem" : es)) = readThm False es
readStmt (List [Atom "input", Atom "string"]) = return $ StepInout (VIKString False)
readStmt (List [Atom "output", Atom "string"]) = return $ StepInout (VIKString True)
readStmt l = Left $ "invalid command " ++ show l

readSortData :: [Lisp] -> Either String SortData
readSortData = \es ->
  case runState (liftM4 SortData (f "pure") (f "strict") (f "provable") (f "free")) es of
    (sd, []) -> return sd
    (_, es') -> Left $ "invalid sort data " ++ show es'
  where
  f s = state $ \case
    Atom s' : es' | s == s' -> (True, es')
    es -> (False, es)

readTerm :: [Lisp] -> Either String Stmt
readTerm [Atom x, List bis, List ret] =
  liftA2 (StmtTerm x) (mapM readBinder bis) (readDepType ret)
readTerm l = Left $ "invalid term " ++ show l

readAxiom :: [Lisp] -> Either String Stmt
readAxiom [Atom x, List bis, List hs, ret] =
  liftA3 (StmtAxiom x) (mapM readBinder bis) (mapM readSExpr hs) (readSExpr ret)
readAxiom l = Left $ "invalid axiom " ++ show l

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
