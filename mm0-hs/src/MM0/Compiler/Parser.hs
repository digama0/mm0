{-# LANGUAGE ScopedTypeVariables #-}
module MM0.Compiler.Parser (parseAST, runParser, PosState(..),
  ParseError, Parser, errorOffset, initialPosState, atPos,
  lispVal, identStart, identRest) where

import Prelude hiding (span)
import Control.Applicative hiding (many, some, (<|>), Const)
import Control.Monad
import Control.Monad.State.Class
import qualified Control.Monad.Trans.State as ST
import Data.Void
import Data.Char
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import Text.Megaparsec hiding (runParser, runParser', ParseError, unPos)
import qualified Text.Megaparsec as MT
import Text.Megaparsec.Char
import qualified Data.Set as S
import qualified Data.Vector as V
import qualified Data.Text as T
import qualified Text.Builder as TB
import qualified Text.Megaparsec.Char.Lexer as L
import MM0.Compiler.AST
import MM0.Util

-- TODO: This should be in Megaparsec
initialPosState :: String -> s -> PosState s
initialPosState name s = PosState s 0 (initialPos name) (mkPos 2) ""

type ParseError = MT.ParseError T.Text Void
type Parser = ParsecT Void T.Text (ST.State [ParseError])

runParser :: Parser a -> String -> Offset -> T.Text -> ([ParseError], Offset, Maybe a)
runParser p n o s =
  let m = setOffset o >> liftA2 (,) p getOffset in
  case ST.runState (runParserT m n s) [] of
    (Left (ParseErrorBundle (l :| ls) pos), errs) ->
      (l : ls ++ errs, pstateOffset pos, Nothing)
    (Right (a, o'), errs) -> (errs, o', Just a)

parseAST :: String -> T.Text -> ([ParseError], Offset, Maybe AST)
parseAST n t = runParser (sc *> (V.fromList <$> stmts)) n 0 t where
  stmts =
    (withRecovery (recoverToSemi Nothing)
        ((do
          o <- getOffset <* kw "exit"
          semi >> failAt o "early exit on 'exit' command"
          return (Just Nothing)) <|>
        (fmap Just <$> spanStmt)) >>= \case
      Just (Just st) -> (st :) <$> stmts
      Just Nothing -> return []
      Nothing -> stmts) <|>
    ([] <$ eof) <?> "expecting command or EOF"

nonFatal :: ParseError -> Parser ()
nonFatal e = modify (e :)

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

spanBracket :: T.Text -> T.Text -> Parser a -> Parser (Span a)
spanBracket l r p = liftA3 (\o1 a o2 -> Span (o1, o2 + 1) a)
  (getOffset <* symbol l) p (getOffset <* symbol r)

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

kw :: T.Text -> Parser ()
kw w = lexeme $ try $ string w *> notFollowedBy alphaNumChar

okw :: T.Text -> Parser Bool
okw w = isJust <$> optional (kw w)

atPos :: Parser a -> Parser (AtPos a)
atPos = liftA2 AtPos getOffset

span :: Parser a -> Parser (Span a)
span p = liftA3 (\o1 a o2 -> Span (o1, o2) a) getOffset p getOffset

mSpan :: Parser (Maybe (a, Offset)) -> Parser (Maybe (Span a))
mSpan = liftA2 (fmap . (\o (a, o2) -> Span (o, o2) a)) getOffset

spanStmt :: Parser (Maybe (Span Stmt))
spanStmt = sortStmt <|> declStmt <|> thmsStmt <|>
  mSpan (fmap (mapFst Notation) <$> notation) <|>
  mSpan (fmap (mapFst Inout) <$> inout) <|>
  annot <|> doStmt

identStart :: Char -> Bool
identStart c = isAlpha c || c == '_'

identRest :: Char -> Bool
identRest c = isAlphaNum c || c == '_'

ident_' :: Parser T.Text
ident_' = liftA2 T.cons (satisfy identStart)
  (takeWhileP (Just "identifier char") identRest)

ident_ :: Parser T.Text
ident_ = lexeme ident_'

ident :: Parser T.Text
ident = ident_ >>= \case "_" -> empty; i -> return i

ident' :: Parser T.Text
ident' = ident_' >>= \case "_" -> empty; i -> return i

recoverToSemi :: a -> ParseError -> Parser a
recoverToSemi a err = takeWhileP Nothing (/= ';') >> semi >> a <$ nonFatal err

commit' :: Parser (Maybe a) -> Parser (Maybe (a, Offset))
commit' p = withRecovery (recoverToSemi Nothing)
  (liftA2 (\a o -> flip (,) (o+1) <$> a) p getOffset <* semi)

commit :: Parser a -> Parser (Maybe (a, Offset))
commit p = commit' (Just <$> p)

toSpan :: (AtPos a, Offset) -> Span a
toSpan (AtPos o a, o2) = Span (o, o2) a

sortData :: Parser SortData
sortData = liftM4 SortData
  (okw "pure") (okw "strict") (okw "provable") (okw "free")

sortStmt :: Parser (Maybe (Span Stmt))
sortStmt = fmap toSpan <$> do
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

formula' :: Parser Formula
formula' = between (single '$') (single '$') $
  liftA2 Formula getOffset (takeWhileP Nothing (/= '$'))

formula :: Parser Formula
formula = lexeme formula'

depType :: Parser AtDepType
depType = (\(t:vs) -> AtDepType t vs) <$> some (lexeme (span ident'))

ptype :: Parser Type
ptype = (TFormula <$> formula) <|> (TType <$> depType)

binder :: Parser [Binder]
binder = braces (f LBound) <|> parens (f LReg) where
  f :: (T.Text -> Local) -> Parser [Binder]
  f bd = liftA2 mk
    (some (liftA3 (\o m (Span (_, o2) i) -> Span (o, o2) $ local' bd m i)
      getOffset (optional (symbol ".")) (lexeme (span ident_'))))
    (optional (symbol ":" *> ptype))
  local' :: (T.Text -> Local) -> Maybe () -> T.Text -> Local
  local' _ _ "_" = LAnon
  local' _ (Just _) x = LDummy x
  local' g Nothing x = g x
  mk :: [Span Local] -> Maybe Type -> [Binder]
  mk [] _ = []
  mk (Span loc l : ls) ty = Binder loc l ty : mk ls ty

binders :: Parser [Binder]
binders = concat <$> many binder

declStmt :: Parser (Maybe (Span Stmt))
declStmt = fmap toSpan <$> do
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
  checkBinders dk _ (Binder (o, _) l (Just (TFormula _)) : bis) | isLCurly l =
    (o, "Use regular binders for formula hypotheses") :
    checkBinders dk (Just o) bis
  checkBinders dk _ (Binder (o, _) _ (Just (TFormula _)) : bis) =
    if dk == DKTerm || dk == DKDef then
      [(o, "A term/def does not take formula hypotheses")] else [] ++
    checkBinders dk (Just o) bis
  checkBinders dk loff (Binder (o, _) _ Nothing : bis) =
    if dk == DKTerm then [(o, "Cannot infer binder type")] else [] ++
    checkBinders dk loff bis
  checkBinders dk off (Binder (o2, _) l (Just (TType (AtDepType _ ts))) : bis) =
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

thmsStmt :: Parser (Maybe (Span Stmt))
thmsStmt = mSpan $ kw "theorems" *>
  commit (liftA2 Theorems binders (symbol "=" *> braces (many lispVal)))

prec :: Parser Prec
prec = (PrecMax <$ kw "max") <|> (do
  o <- getOffset
  n :: Integer <- lexeme L.decimal
  if n < fromIntegral (maxBound :: Int) then
    return (Prec (fromIntegral n))
  else PrecMax <$ failAt o "precedence out of range")

notation :: Parser (Maybe (Notation, Offset))
notation = delimNota <|> fixNota <|> coeNota <|> genNota where

  delimNota :: Parser (Maybe (Notation, Offset))
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

  fixNota :: Parser (Maybe (Notation, Offset))
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

  coeNota :: Parser (Maybe (Notation, Offset))
  coeNota = kw "coercion" >> commit
    (liftM4 Coercion getOffset ident (symbol ":" *> ident) (symbol ">" >> ident))

  genNota :: Parser (Maybe (Notation, Offset))
  genNota = kw "notation" >> commit
    (liftM5 NNotation getOffset ident binders
      (optional (symbol ":" *> ptype))
      (symbol "=" *> some (atPos $
        parens (liftA2 NConst constant (symbol ":" *> prec)) <|>
        (NVar <$> ident))))

inout :: Parser (Maybe (Inout, Offset))
inout = do
  mk <- (Input <$ kw "input") <|> (Output <$ kw "output")
  commit $ liftA2 mk ident (many lispVal)

annot :: Parser (Maybe (Span Stmt))
annot = mSpan (symbol "@" >>
  liftA2 (fmap . \v s@(Span o _) -> (Annot v s, snd o)) lispVal spanStmt)

doStmt :: Parser (Maybe (Span Stmt))
doStmt = mSpan (kw "do" >> commit (braces (Do <$> many lispVal)))

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

lispVal :: Parser AtLisp
lispVal =
  spanBracket "(" ")" listVal <|>
  spanBracket "[" "]" listVal <|>
  (toCurlyList <$> spanBracket "{" "}" listVal) <|>
  (fmap ANumber <$> lexeme (span L.decimal)) <|>
  (fmap AString <$> lexeme (span strLit)) <|>
  (fmap AFormula <$> lexeme (span formula')) <|>
  (liftA2 (\(Span o _) v@(Span (_, o2) _) ->
    Span (fst o, o2) $ AList [Span o (AAtom False "quote"), v]) (span (single '\'')) lispVal) <|>
  (liftA2 (\(Span o _) v@(Span (_, o2) _) ->
    Span (fst o, o2) $ AList [Span o (AAtom False "unquote"), v]) (span (single ',')) lispVal) <|>
  (lexeme (span (single '#' *> takeWhileP (Just "identifier char") lispIdent >>= hashAtom))) <|>
  (lexeme (span (takeWhileP (Just "identifier char") lispIdent >>= atom)))

listVal :: Parser LispAST
listVal =
  (lexeme "@" *> ((\e -> AList [e]) <$> span listVal)) <|>
  listVal1 <|> return (AList [])
  where
  listVal1 = lispVal >>= \l ->
    (ADottedList l [] <$> (lexeme "." *> lispVal)) <|>
    (cons l <$> listVal)

cons :: AtLisp -> LispAST -> LispAST
cons l (AList r) = AList (l : r)
cons l (ADottedList r0 rs r) = ADottedList l (r0 : rs) r
cons _ _ = error "impossible"

toCurlyList :: AtLisp -> AtLisp
toCurlyList s@(Span _ (AList [])) = s
toCurlyList (Span _ (AList [e])) = e
toCurlyList s@(Span _ (AList [_, _])) = s
toCurlyList (Span r (AList [e1, op, e2])) = Span r (AList [op, e1, e2])
toCurlyList (Span r@(o, _) e@(AList (e1 : op@(Span _ (AAtom _ tk)) : es))) =
  case go es of
    Nothing -> Span r (cons (Span (o, o + 1) (AAtom False ":nfx")) e)
    Just es' -> Span r (AList (op : e1 : es'))
  where
  go [e2] = Just [e2]
  go (e2 : Span _ (AAtom _ tk') : es') | tk' == tk = (e2 :) <$> go es'
  go _ = Nothing
toCurlyList (Span r@(o, _) e) =
  (Span r (cons (Span (o, o + 1) (AAtom False ":nfx")) e))

hashAtom :: T.Text -> Parser LispAST
hashAtom "t" = return (ABool True)
hashAtom "f" = return (ABool False)
hashAtom _ = empty

atom :: T.Text -> Parser LispAST
atom t = if legalIdent then return (AAtom False t) else empty where
  legalIdent = t `elem` ["+", "-", "..."] ||
    case T.uncons t of
      Nothing -> False
      Just (c, _) ->
        (c `notElem` ("+-.@" :: String) && not (isDigit c)) ||
        T.isPrefixOf "->" t
