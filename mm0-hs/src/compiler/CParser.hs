{-# LANGUAGE ScopedTypeVariables #-}
module CParser (parseAST, runParser, PosState(..),
  ParseError, Parser, errorOffset, initialPosState, atPos,
  lispVal, identStart, identRest) where

import Control.Applicative hiding (many, some, (<|>), Const)
import Control.Monad
import Control.Monad.Trans.Class
import qualified Control.Monad.Trans.State as ST
import Data.Void
import Data.Char
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import Text.Megaparsec hiding (runParser, runParser', ParseError)
import qualified Text.Megaparsec as MT
import Text.Megaparsec.Char
import Control.Monad.Trans.State
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Text.Builder as TB
import qualified Text.Megaparsec.Char.Lexer as L
import CAST

-- TODO: This should be in Megaparsec
initialPosState :: String -> s -> PosState s
initialPosState name s = PosState s 0 (initialPos name) (mkPos 2) ""

type ParsecST e s m = ParsecT e s (StateT [MT.ParseError s e] m)
type ParseError = MT.ParseError T.Text Void
type Parser = ParsecT Void T.Text (ST.State [ParseError])

runParser :: Parser a -> String -> Offset -> T.Text -> ([ParseError], Offset, Maybe a)
runParser p n o s =
  case runState (runParserT (setOffset o >> liftA2 (,) p getOffset) n s) [] of
    (Left (ParseErrorBundle (l :| ls) pos), errs) ->
      (l : ls ++ errs, pstateOffset pos, Nothing)
    (Right (a, o'), errs) -> (errs, o', Just a)

parseAST :: String -> T.Text -> ([ParseError], Offset, Maybe AST)
parseAST n t = runParser (sc *> stmts) n 0 t where
  stmts =
    (withRecovery (recoverToSemi Nothing) atStmt >>= \case
      Just st -> (st :) <$> stmts
      _ -> stmts) <|>
    ([] <$ eof) <?> "expecting command or EOF"

nonFatal :: Monad m => MT.ParseError s e -> ParsecST e s m ()
nonFatal e = lift (modify (e :))

failAt :: Int -> String -> Parser ()
failAt o s = nonFatal $ FancyError o (S.singleton (ErrorFail s))

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: T.Text -> Parser ()
symbol s = () <$ L.symbol sc s

semi :: Parser ()
semi = symbol ";"

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

kw :: T.Text -> Parser ()
kw w = lexeme $ try $ string w *> notFollowedBy alphaNumChar

okw :: T.Text -> Parser Bool
okw w = isJust <$> optional (kw w)

atPos :: Parser a -> Parser (AtPos a)
atPos = liftA2 AtPos getOffset

mAtPos :: Parser (Maybe a) -> Parser (Maybe (AtPos a))
mAtPos = liftA2 (fmap . AtPos) getOffset

atStmt :: Parser (Maybe (AtPos Stmt))
atStmt = sortStmt <|> declStmt <|> thmsStmt <|>
  mAtPos (fmap Notation <$> notation) <|>
  mAtPos (fmap Inout <$> inout) <|>
  annot <|> doStmt

identStart :: Char -> Bool
identStart c = isAlpha c || c == '_'

identRest :: Char -> Bool
identRest c = isAlphaNum c || c == '_'

ident_ :: Parser T.Text
ident_ = lexeme $ liftA2 T.cons (satisfy identStart)
  (takeWhileP (Just "identifier char") identRest)

ident :: Parser T.Text
ident = ident_ >>= \case "_" -> empty; i -> return i

recoverToSemi :: a -> ParseError -> Parser a
recoverToSemi a err = takeWhileP Nothing (/= ';') >> semi >> a <$ nonFatal err

commit' :: Parser (Maybe a) -> Parser (Maybe a)
commit' p = withRecovery (recoverToSemi Nothing) (p <* semi)

commit :: Parser a -> Parser (Maybe a)
commit p = commit' (Just <$> p)

sortData :: Parser SortData
sortData = liftM4 SortData
  (okw "pure") (okw "strict") (okw "provable") (okw "free")

sortStmt :: Parser (Maybe (AtPos Stmt))
sortStmt = do
  sd <- sortData
  ostmt <- getOffset <* kw "sort"
  commit $ do
    o <- getOffset
    x <- ident
    return $ AtPos ostmt (Sort o x sd)

constant :: Parser Const
constant = between (symbol "$") (symbol "$") $
  liftA2 Const getOffset $
    lexeme (takeWhileP Nothing (\c -> c /= '$' && not (isSpace c)))

formula :: Parser Formula
formula = lexeme $ between (single '$') (single '$') $
  liftA2 Formula getOffset (takeWhileP Nothing (/= '$'))

depType :: Parser AtDepType
depType = (\(t:vs) -> AtDepType t vs) <$> some (atPos ident)

ptype :: Parser Type
ptype = (TFormula <$> formula) <|> (TType <$> depType)

binder :: Parser [Binder]
binder = braces (f LBound) <|> parens (f LReg) where
  f :: (T.Text -> Local) -> Parser [Binder]
  f bd = liftA2 mk
    (some (atPos (liftA2 (local bd) (optional (symbol ".")) ident_)))
    (optional (symbol ":" *> ptype))
  local :: (T.Text -> Local) -> Maybe () -> T.Text -> Local
  local _ _ "_" = LAnon
  local _ (Just _) x = LDummy x
  local g Nothing x = g x
  mk :: [AtPos Local] -> Maybe Type -> [Binder]
  mk [] _ = []
  mk (AtPos loc l : ls) ty = Binder loc l ty : mk ls ty

binders :: Parser [Binder]
binders = concat <$> many binder

declStmt :: Parser (Maybe (AtPos Stmt))
declStmt = do
  ovis <- getOffset
  vis <- (Public <$ kw "pub") <|> (Abstract <$ kw "abstract") <|>
         (Local <$ kw "local") <|> return VisDefault
  ostmt <- getOffset
  dk <- (DKTerm <$ kw "term") <|> (DKAxiom <$ kw "axiom") <|>
        (DKTheorem <$ kw "theorem") <|> (DKDef <$ kw "def")
  commit' $ do
    px <- getOffset
    x <- ident
    bis <- binders
    ret <- optional (symbol ":" *> sepBy1 ptype (symbol ">"))
    let errs = maybe [] (checkRet dk) ret ++ checkBinders dk Nothing bis
    o <- getOffset
    val <- optional (symbol "=" *> lispVal)
    let {errs' = case (val, ret, vis, dk) of
      (Just _, Just (_:_:_), _, _) ->
        (o, "Arrow type notation is not allowed with '='." <>
            " Use anonymous binders '(_ : foo)' instead") : errs
      (Nothing, Nothing, _, _) -> (o, "Cannot infer return type") : errs
      (Just _, _, _, DKTerm) -> (o, "A term does not take a definition") : errs
      (Just _, _, _, DKAxiom) -> (o, "An axiom does not take a proof") : errs
      (_, Nothing, _, DKTheorem) ->
        (o, "Inferring theorem statements is not supported") : errs
      (_, _, Abstract, _) | dk /= DKDef ->
        (ovis, "Only definitions take the 'abstract' keyword") : errs
      (_, _, _, DKAxiom) | vis /= VisDefault ->
        (ovis, "Axioms do not take a visibility modifier (they are always public)") : errs
      (_, _, _, DKTerm) | vis /= VisDefault ->
        (ovis, "Terms do not take a visibility modifier (they are always public)") : errs
      _ -> errs}
    if null errs' then
      return $ Just (AtPos ostmt (Decl vis dk px x bis ret val))
    else Nothing <$ mapM_ (\(o', msg) -> failAt o' msg) errs'
  where

  checkBinders :: DeclKind -> Maybe Offset -> [Binder] -> [(Offset, String)]
  checkBinders _ _ [] = []
  checkBinders dk _ (Binder o l (Just (TFormula _)) : bis) | isLCurly l =
    (o, "Use regular binders for formula hypotheses") :
    checkBinders dk (Just o) bis
  checkBinders dk _ (Binder o _ (Just (TFormula _)) : bis) =
    if dk == DKTerm || dk == DKDef then
      [(o, "A term/def does not take formula hypotheses")] else [] ++
    checkBinders dk (Just o) bis
  checkBinders dk loff (Binder o _ Nothing : bis) =
    if dk == DKTerm then [(o, "Cannot infer binder type")] else [] ++
    checkBinders dk loff bis
  checkBinders dk off (Binder o2 l (Just (TType (AtDepType _ ts))) : bis) =
    maybe [] (\o ->
      [(o, "Hypotheses must come after term variables"),
       (o2, "All term variables must come before all hypotheses")]) off ++
    if isLCurly l && not (null ts) then
      [(o2, "Bound variable has dependent type")] else [] ++
    checkBinders dk Nothing bis

  checkRet :: DeclKind -> [Type] -> [(Offset, String)]
  checkRet _ [] = []
  checkRet dk [t@(TFormula _)] =
    if dk == DKTerm || dk == DKDef then
      [(tyOffset t, "A term/def does not return a formula")] else []
  checkRet dk (t@(TFormula _) : tys) =
    if dk == DKTerm || dk == DKDef then
      [(tyOffset t, "A term/def does not take formula hypotheses")] else [] ++
    checkRet dk tys
  checkRet dk (_ : tys) = checkRet dk tys

thmsStmt :: Parser (Maybe (AtPos Stmt))
thmsStmt = mAtPos $ kw "theorems" *>
  commit (liftA2 Theorems binders (symbol "=" *> braces (many lispVal)))

prec :: Parser Prec
prec = (PrecMax <$ kw "max") <|> (do
  o <- getOffset
  n :: Integer <- lexeme L.decimal
  if n < fromIntegral (maxBound :: Int) then
    return (Prec (fromIntegral n))
  else PrecMax <$ failAt o "precedence out of range")

notation :: Parser (Maybe Notation)
notation = delimNota <|> fixNota <|> coeNota <|> genNota where

  delimNota :: Parser (Maybe Notation)
  delimNota = do
    kw "delimiter"
    let p = between (single '$') (symbol "$") (space *> delims)
    commit $ liftA2 Delimiter p (optional p)
    where
    delims :: Parser [Char]
    delims = do
      o <- getOffset
      T.unpack <$> takeWhileP (Just "math character") (\c -> c /= '$' && not (isSpace c)) >>= \case
        [] -> return []
        [c] -> space >> (c :) <$> delims
        _ -> do
          failAt o "multiple character delimiters not supported"
          space >> delims

  fixNota :: Parser (Maybe Notation)
  fixNota = do
    mk <- (Prefix <$ kw "prefix") <|>
      (Infix False <$ kw "infixl") <|> (Infix True <$ kw "infixr")
    commit $ do
      mk' <- liftM3 mk getOffset ident (symbol ":" *> constant) <* kw "prec"
      o <- getOffset
      mk' <$> prec >>= \case
        r@(Infix _ _ _ _ PrecMax) -> do
          failAt o "infix prec max not allowed"
          return r
        r -> return r

  coeNota :: Parser (Maybe Notation)
  coeNota = kw "coercion" >> commit
    (liftM3 Coercion ident (symbol ":" *> ident) (symbol ">" >> ident))

  genNota :: Parser (Maybe Notation)
  genNota = kw "notation" >> commit
    (liftM4 NNotation ident binders
      (optional (symbol ":" *> ptype))
      (symbol "=" *> many (
        parens (liftA2 NConst constant (symbol ":" *> prec)) <|>
        (NVar <$> ident))))

inout :: Parser (Maybe Inout)
inout = do
  mk <- (Input <$ kw "input") <|> (Output <$ kw "output")
  commit $ liftA2 mk ident (many lispVal)

annot :: Parser (Maybe (AtPos Stmt))
annot = mAtPos (symbol "@" >> liftA2 (fmap . Annot) lispVal atStmt)

doStmt :: Parser (Maybe (AtPos Stmt))
doStmt = mAtPos (kw "do" >> commit (braces (Do <$> many lispVal)))

strLit :: Parser T.Text
strLit = single '"' *> (TB.run <$> p) where
  p = do
    toks <- TB.text <$>
      takeWhileP (Just "end of string") (\c -> c /= '\\' && c /= '"')
    let f from to = single from *> ((TB.char to <>) . (toks <>) <$> p)
    (toks <$ single '"') <|> (single '\\' *>
      (f '"' '"' <|> f '\\' '\\' <|> f 'n' '\n' <|> f 'r' '\r'))

lispIdent :: Char -> Bool
lispIdent c = isAlphaNum c || c `elem` ("!%&*/:<=>?^_~+-.@" :: String)

lispVal :: Parser LispVal
lispVal = parens listVal <|>
  (Number <$> lexeme L.decimal) <|>
  (String <$> lexeme strLit) <|>
  (LFormula <$> formula) <|>
  (single '\'' *> ((\v -> List [Atom "quote", v]) <$> lispVal)) <|>
  (lexeme (single '#' *> takeWhileP (Just "identifier char") lispIdent >>= hashAtom)) <|>
  (lexeme (takeWhileP (Just "identifier char") lispIdent >>= atom))

listVal :: Parser LispVal
listVal = listVal1 <|> return (List []) where
  listVal1 = lispVal >>= \l ->
    cons l <$> ((lexeme "." *> lispVal) <|> listVal)

hashAtom :: T.Text -> Parser LispVal
hashAtom "t" = return (Bool True)
hashAtom "f" = return (Bool False)
hashAtom _ = empty

atom :: T.Text -> Parser LispVal
atom t = if legalIdent t then return (Atom t) else empty where
  legalIdent t' = t' `elem` ["+", "-", "..."] ||
    case T.unpack t' of
      '-' : '>' : s -> all (`notElem` ("+-.@" :: String)) s
      c : s -> not (isDigit c) && all (`notElem` ("+-.@" :: String)) s
      [] -> False
