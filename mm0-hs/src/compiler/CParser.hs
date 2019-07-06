{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
module CParser (parseAST, ParseASTError) where

import Control.Applicative hiding (many, some, (<|>), Const)
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans.Class
import Control.Monad.Trans.State (StateT, runStateT)
import Data.Void
import Data.Char
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import Text.Megaparsec
import Text.Megaparsec.Char
import Control.Monad.Trans.State
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Text.Builder as TB
import qualified Text.Megaparsec.Char.Lexer as L
import CAST
import Util

type ParsecST e s m = ParsecT e s (StateT [ParseError s e] m)

-- TODO: This should be in Megaparsec
initialPosState :: String -> s -> PosState s
initialPosState name s = PosState
  { pstateInput = s
  , pstateOffset = 0
  , pstateSourcePos = initialPos name
  , pstateTabWidth = defaultTabWidth
  , pstateLinePrefix = ""
  }

-- TODO: This should be in Megaparsec
runParserST :: forall m s e a. Monad m =>
  ParsecST e s m a -> String -> s -> m (Either (ParseErrorBundle s e, Maybe a) a)
runParserST p n s = merge <$> runStateT (runParserT p n s) [] where
  merge :: (Either (ParseErrorBundle s e) a, [ParseError s e]) ->
      Either (ParseErrorBundle s e, Maybe a) a
  merge (Right a, []) = Right a
  merge (Left e, []) = Left (e, Nothing)
  merge (Right a, e : es) = Left (build es e [] (initialPosState n s), Just a)
  merge (Left (ParseErrorBundle (l :| ls) pos), e : es) =
    Left (build es e (l : ls) pos, Nothing)
  build :: [ParseError s e] -> ParseError s e ->
    [ParseError s e] -> PosState s -> ParseErrorBundle s e
  build [] l ls = ParseErrorBundle (l :| ls)
  build (e : es) l ls = build es e (l : ls)

nonFatal :: Monad m => ParseError s e -> ParsecST e s m ()
nonFatal e = lift (modify (e :))

runParserS :: ParsecST e s Identity a -> String -> s -> Either (ParseErrorBundle s e, Maybe a) a
runParserS p n s = runIdentity (runParserST p n s)

type Parser = ParsecST Void T.Text Identity
type ParseASTError = ParseErrorBundle T.Text Void

parseAST :: T.Text -> Either (ParseASTError, Maybe AST) AST
parseAST = runParserS (sc *> stmts) "" where
  stmts =
    (withRecovery (recoverToSemi Nothing) (Just <$> atPos stmt) >>= \case
      Just (AtPos pos (Just e)) -> (AtPos pos e :) <$> stmts
      _ -> stmts) <|>
    ([] <$ eof) <?> "expecting command or EOF"

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
atPos = liftA2 AtPos getSourcePos

stmt :: Parser (Maybe Stmt)
stmt = sortStmt <|> declStmt <|> thmsStmt <|>
  (fmap Notation <$> notation) <|> (fmap Inout <$> inout) <|>
  annot <|> doStmt

identStart :: Char -> Bool
identStart c = isAlpha c || c == '_'

identRest :: Char -> Bool
identRest c = isAlphaNum c || c == '_'

ident :: Parser Ident
ident = lexeme $ liftA2 (:) (satisfy identStart)
  (T.unpack <$> takeWhileP (Just "identifier char") identRest)

recoverToSemi :: a -> ParseError T.Text Void -> Parser a
recoverToSemi a err = takeWhileP Nothing (/= ';') >> semi >> a <$ nonFatal err

commit :: Parser a -> Parser (Maybe a)
commit p = withRecovery (recoverToSemi Nothing) (Just <$> (p <* semi))

sortData :: Parser SortData
sortData = liftM4 SortData
  (okw "pure") (okw "strict") (okw "provable") (okw "free")

sortStmt :: Parser (Maybe Stmt)
sortStmt = do
  sd <- sortData <* kw "sort"
  commit $ flip Sort sd <$> ident <|> fail "NOOO"

type DeclStmt = Ident -> [Binder] -> Maybe ([AtPos Type], Type) -> Parser Stmt

constant :: Parser Const
constant = between (symbol "$") (symbol "$") $
  Const <$> lexeme (takeWhileP Nothing (\c -> c /= '$' && not (isSpace c)))

formula :: Parser Formula
formula = lexeme $ between (single '$') (single '$') $
  liftA2 Formula getSourcePos (takeWhileP Nothing (/= '$'))

depType :: Parser DepType
depType = (\(t:vs) -> DepType t vs) <$> some (atPos ident)

ptype :: Parser Type
ptype = (TFormula <$> formula) <|> (TType <$> depType)

binder :: Parser [Binder]
binder = braces (f LBound) <|> parens (f LReg) where
  f :: (Ident -> Local) -> Parser [Binder]
  f bd = liftA2 mk
    (some (atPos (liftA2 (local bd) (optional (symbol ".")) ident)))
    (optional (symbol ":" *> ptype))
  local :: (Ident -> Local) -> Maybe () -> Ident -> Local
  local _ _ "_" = LAnon
  local _ (Just _) x = LDummy x
  local f Nothing x = f x
  mk :: [AtPos Local] -> Maybe Type -> [Binder]
  mk [] _ = []
  mk (AtPos loc l : ls) ty = Binder loc l ty : mk ls ty

binders :: Parser [Binder]
binders = concat <$> many binder

declStmt :: Parser (Maybe Stmt)
declStmt = do
  vis <- (Public <$ kw "pub") <|> (Abstract <$ kw "abstract") <|>
         (Local <$ kw "local") <|> return VisDefault
  dk <- (DKTerm <$ kw "term") <|> (DKAxiom <$ kw "axiom") <|>
        (DKTheorem <$ kw "theorem") <|> (DKDef <$ kw "def")
  commit $ liftM4 (Decl vis dk) ident binders
    (optional (symbol ":" *> sepBy1 ptype (symbol ">")))
    (optional (symbol "=" *> lispVal))

thmsStmt :: Parser (Maybe Stmt)
thmsStmt = kw "theorems" *>
  commit (liftA2 Theorems binders (symbol "=" *> braces (many lispVal)))

prec :: Parser Prec
prec = (maxBound <$ kw "max") <|> (do
  o <- getOffset
  n <- lexeme L.decimal
  if n < fromIntegral (maxBound :: Int) then
    return (fromIntegral n)
  else maxBound <$ failAt o "precedence out of range")

notation :: Parser (Maybe Notation)
notation = delimNota <|> fixNota <|> coeNota <|> genNota where

  delimNota :: Parser (Maybe Notation)
  delimNota = kw "delimiter" >> commit
    (between (single '$') (symbol "$")
      (space *> (Delimiter <$> delims)))
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
    commit $ liftM3 mk ident (symbol ":" *> constant) (kw "prec" *> prec)

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

annot :: Parser (Maybe Stmt)
annot = symbol "@" >> liftA2 (fmap . Annot) lispVal stmt

doStmt :: Parser (Maybe Stmt)
doStmt = kw "do" >> commit (braces (Do <$> many lispVal))

strLit :: Parser T.Text
strLit = single '"' *> (TB.run <$> p) where
  p = do
    chunk <- TB.text <$>
      takeWhileP (Just "end of string") (\c -> c /= '\\' && c /= '"')
    let f from to = single from *> ((TB.char to <>) . (chunk <>) <$> p)
    (chunk <$ single '"') <|> (single '\\' *>
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
  legalIdent t = t `elem` ["+", "-", "..."] ||
    case T.unpack t of
      '-' : '>' : s -> all (`notElem` ("+-.@" :: String)) s
      c : s -> not (isDigit c) && all (`notElem` ("+-.@" :: String)) s
      [] -> False
