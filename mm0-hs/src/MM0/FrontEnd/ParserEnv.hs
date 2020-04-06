module MM0.FrontEnd.ParserEnv (Token,
  PLiteral(..),
  ParserEnv(..),
  NotaInfo(..),
  addNotation, recalcCoeProv, tokenize, getCoe, getCoeProv) where

import Control.Monad.Except
import Control.Monad.Trans.State
import Control.Applicative ((<|>))
import Data.List
import Data.List.Split
import Data.Maybe
import Data.Default
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import MM0.FrontEnd.AST
import MM0.Kernel.Environment
import MM0.Util

data PLiteral = PConst Token | PVar Int Prec deriving (Show)

data NotaInfo = NotaInfo {
  niTerm :: TermName,
  niLits :: (Maybe (Int, Prec), [PLiteral]),
  niRAssoc :: Maybe Bool } deriving (Show)
type Coe = SExpr -> SExpr

data ParserEnv = ParserEnv {
  delims :: S.Set Char,
  prefixes :: M.Map Token NotaInfo,
  infixes :: M.Map Token NotaInfo,
  prec :: M.Map Token Prec,
  coes :: M.Map Ident (M.Map Ident Coe),
  coeProv :: M.Map Ident Ident }

instance Default ParserEnv where
  def = ParserEnv def def def def def def

tokenize :: ParserEnv -> T.Text -> [Token]
tokenize pe cnst = concatMap go (splitOneOf " \n" (T.unpack cnst)) where
  ds = delims pe
  go :: String -> [Token]
  go [] = []
  go (c:s) = go1 c s id
  go1 :: Char -> String -> (String -> String) -> [Token]
  go1 c s f | S.member c ds = case f [] of
    [] -> T.singleton c : go s
    s1 -> T.pack s1 : T.singleton c : go s
  go1 c [] f = [T.pack $ f [c]]
  go1 c (c':s) f = go1 c' s (f . (c:))

tokenize1 :: ParserEnv -> Const -> Either String Token
tokenize1 env (Const cnst) = case tokenize env cnst of
  [tk] -> return tk
  tks -> throwError ("bad token" ++ show tks)

checkToken :: ParserEnv -> Token -> Bool
checkToken e tk =
  if T.length tk == 1 then
      T.head tk `notElem` (" \n"::String)
  else T.all (\c -> c `S.notMember` delims e && c `notElem` (" \n"::String)) tk

mkLiterals :: Int -> Prec -> Int -> [PLiteral]
mkLiterals 0 _ _ = []
mkLiterals 1 p n = [PVar n p]
mkLiterals i p n = PVar n maxBound : mkLiterals (i-1) p (n+1)

insertPrec :: Token -> Prec -> ParserEnv -> Either String ParserEnv
insertPrec tk p e = do
  guardError ("incompatible precedence for " ++ T.unpack tk)
    (maybe True (p ==) (prec e M.!? tk))
  return (e {prec = M.insert tk p (prec e)})

insertPrefixInfo :: Token -> NotaInfo -> ParserEnv -> Either String ParserEnv
insertPrefixInfo tk ti e = do
  guardError ("invalid token '" ++ T.unpack tk ++ "'") (checkToken e tk)
  ts <- insertNew ("token '" ++ T.unpack tk ++ "' already declared") tk ti (prefixes e)
  return (e {prefixes = ts})

insertInfixInfo :: Token -> NotaInfo -> ParserEnv -> Either String ParserEnv
insertInfixInfo tk ti e = do
  guardError ("invalid token '" ++ T.unpack tk ++ "'") (checkToken e tk)
  ts <- insertNew ("token '" ++ T.unpack tk ++ "' already declared") tk ti (infixes e)
  return (e {infixes = ts})

matchBinders :: [Binder] -> DepType -> ([PBinder], DepType) -> Bool
matchBinders bs2 r' (bs1, r) = go bs1 bs2 where
  go :: [PBinder] -> [Binder] -> Bool
  go [] [] = r == r'
  go (PBound b t : bs) (Binder (LBound b') (TType (DepType t' [])) : bs') =
    b == b' && t == t' && go bs bs'
  go (PReg b ty : bs) (Binder (LReg b') (TType ty') : bs') =
    b == b' && ty == ty' && go bs bs'
  go _ _ = False

processLits :: TermName -> [Binder] -> [Literal] -> Maybe (Prec, Bool) ->
  StateT ParserEnv (Either String) (Bool, Token, NotaInfo)
processLits x bis = \lits prec1 -> do
  (llit, lits', rassoc, inf, tk, prec) <- lift $ case lits of
    [] -> throwError "notation requires at least one literal"
    NConst c p : lits1 -> return (Nothing, lits1, Just True, False, c, p)
    [NVar _] -> throwError "notation requires at least one constant"
    NVar _ : NVar _ : _ -> throwError "notation cannot start with two variables"
    NVar v : NConst c p : lits1 -> do
      r <- case prec1 of
        Nothing -> return Nothing
        Just (q, _) | q /= p -> throwError "notation precedence must match first constant"
        Just (_, r) -> return (Just r)
      n <- findVar v
      q <- bump (fromMaybe False r) p
      return (Just (n, q), lits1, r, True, c, p)
  tk' <- processConst tk prec
  let
    go :: [Literal] -> Maybe Bool -> StateT ParserEnv (Either String) ([PLiteral], Maybe Bool)
    go [] r = return ([], r)
    go (NConst c p : lits) r = do
      tk <- processConst c p
      go lits r <&> \(l, r') -> (PConst tk : l, r')
    go (NVar v : lits) r = do
      (q, r2) <- lift $ case lits of
        [] -> do
          r2 <- fromJustError "general infix notation requires explicit associativity" $
            (r <|> (snd <$> prec1))
          (,Just r2) <$> bump (not r2) prec
        (NConst _ q : _) -> (,r) <$> bump True q
        (NVar _ : _) -> return (maxBound, r)
      n <- lift $ findVar v
      go lits r2 <&> \(l, r') -> (PVar n q : l, r')
  (plits, r') <- go lits' rassoc
  return (inf, tk', NotaInfo x (llit, plits) r')
  where

  processConst :: Const -> Prec -> StateT ParserEnv (Either String) Token
  processConst c' p' = StateT $ \e -> do
    tk <- tokenize1 e c'
    e' <- insertPrec tk p' e
    return (tk, e')

  findVar :: Ident -> Either String Int
  findVar v = fromJustError "notation variable not found" $
    findIndex (\(Binder l _) -> localName l == Just v) bis

bump :: Bool -> Prec -> Either String Prec
bump False p = return p
bump True p | p < maxBound = return (p + 1)
bump True _ = throwError "notation infix prec max not allowed"

getCoe :: Ident -> Ident -> ParserEnv -> Maybe Coe
getCoe s1 s2 _ | s1 == s2 = Just id
getCoe s1 s2 e = coes e M.!? s1 >>= (M.!? s2)

getCoeProv :: Ident -> ParserEnv -> Maybe (Ident, Coe)
getCoeProv s e = do
  s2 <- coeProv e M.!? s
  c <- getCoe s s2 e
  Just (s2, c)

foldCoeLeft :: Ident -> ParserEnv -> (Ident -> Coe -> a -> a) -> a -> a
foldCoeLeft s2 e f a = M.foldrWithKey' g a (coes e) where
  g s1 m a' = maybe a' (\l -> f s1 l a) (m M.!? s2)

foldCoeRight :: Ident -> ParserEnv -> (Ident -> Coe -> a -> a) -> a -> a
foldCoeRight s1 e f a = maybe a (M.foldrWithKey' f a) (coes e M.!? s1)

addCoeInner :: Ident -> Ident -> Coe -> ParserEnv -> Either String ParserEnv
addCoeInner s1 s2 l e = do
  guardError "coercion cycle detected" (s1 /= s2)
  guardError "coercion diamond detected" (isNothing $ getCoe s1 s2 e)
  let f = M.alter (Just . M.insert s2 l . maybe M.empty id) s1
  return (e {coes = f (coes e)})

addCoe :: Ident -> Ident -> Ident -> ParserEnv -> Either String ParserEnv
addCoe s1 s2 c e = do
  let cc i = App c [i]
  e2 <- foldCoeLeft s1 e (\s1' l r -> r >>= addCoeInner s1' s2 (cc . l)) (return e)
  e3 <- addCoeInner s1 s2 cc e2
  foldCoeRight s2 e3 (\s2' l r -> r >>= addCoeInner s1 s2' (l . cc)) (return e3)

recalcCoeProv :: Environment -> ParserEnv -> Either String ParserEnv
recalcCoeProv env e = do
  m <- M.foldrWithKey' (\s1 m r -> M.foldrWithKey' (f s1) r m)
    (return (S.foldr (\v -> M.insert v v) M.empty provs)) (coes e)
  return (e {coeProv = m})
  where
  provs :: S.Set Ident
  provs = M.keysSet (M.filter sProvable (eSorts env))
  f :: Ident -> Ident -> Coe -> Either String (M.Map Ident Ident) -> Either String (M.Map Ident Ident)
  f s1 s2 _ r = if S.member s2 provs then do
      m <- r
      guardError "coercion diamond to provable detected" (M.notMember s1 m)
      return (M.insert s1 s2 m)
    else r

addNotation :: Notation -> Environment -> ParserEnv -> Either String ParserEnv
addNotation (Delimiter (Const s')) _ e = do
  ds' <- go (splitOneOf " \t\r\n" (T.unpack s')) (delims e)
  return (e {delims = ds'}) where
    go :: [String] -> S.Set Char -> Either String (S.Set Char)
    go [] s = return s
    go ([]:ds) s = go ds s
    go ([c]:ds) s = go ds (S.insert c s)
    go (_:_) _ = throwError "multiple char delimiters not supported"
addNotation (Prefix x s p) env e = do
  n <- fromJustError ("term " ++ T.unpack x ++ " not declared") (getArity env x)
  tk <- tokenize1 e s
  e' <- insertPrec tk p e
  insertPrefixInfo tk (NotaInfo x (Nothing, mkLiterals n p 0) (Just True)) e'
addNotation (Infix r x s p) env e = do
  n <- fromJustError ("term " ++ T.unpack x ++ " not declared") (getArity env x)
  guardError ("'" ++ T.unpack x ++ "' must be a binary operator") (n == 2)
  tk <- tokenize1 e s
  e' <- insertPrec tk p e
  q1 <- bump r p
  q2 <- bump (not r) p
  insertInfixInfo tk (NotaInfo x (Just (0, q1), [PVar 1 q2]) (Just r)) e'
addNotation (NNotation x bi ty lits p) env e = do
  ty' <- fromJustError ("term " ++ T.unpack x ++ " not declared") (getTerm env x)
  guardError ("notation declaration for '" ++ T.unpack x ++ "' must match term") (matchBinders bi ty ty')
  ((inf, tk, ti), e') <- runStateT (processLits x bi lits p) e
  (if inf then insertInfixInfo else insertPrefixInfo) tk ti e'
addNotation (Coercion x s1 s2) env e = do
  fromJustError ("term " ++ T.unpack x ++ " not declared") (getTerm env x) >>= \case
    ([PReg _ (DepType s1' [])], DepType s2' []) | s1 == s1' && s2 == s2' ->
      addCoe s1 s2 x e >>= recalcCoeProv env
    _ -> throwError ("coercion '" ++ T.unpack x ++ "' does not match declaration")
