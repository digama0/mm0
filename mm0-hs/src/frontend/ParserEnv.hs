module ParserEnv(Token,
  PLiteral(..),
  ParserEnv(..),
  PrefixInfo(..),
  InfixInfo(..),
  addNotation, tokenize, getCoe, newParserEnv) where

import Control.Monad.Except
import Control.Monad.Trans.State
import Data.List
import Data.List.Split
import Data.Maybe
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.ByteString.Char8 as C
import AST
import Environment
import Util

type Token = String

data PLiteral = PConst Token | PVar Int Prec deriving (Show)

data PrefixInfo = PrefixInfo Ident [PLiteral] deriving (Show)
data InfixInfo = InfixInfo Ident Bool deriving (Show)
type Coe = SExpr -> SExpr

data ParserEnv = ParserEnv {
  delims :: S.Set Char,
  prefixes :: M.Map Token PrefixInfo,
  infixes :: M.Map Token InfixInfo,
  prec :: M.Map Token Prec,
  coes :: M.Map Ident (M.Map Ident Coe) }

newParserEnv :: ParserEnv
newParserEnv = ParserEnv S.empty M.empty M.empty M.empty M.empty

toString :: Const -> String
toString = C.unpack

tokenize :: ParserEnv -> Formula -> [Token]
tokenize pe cnst = concatMap go (splitOneOf " \t\r\n" (toString cnst)) where
  ds = delims pe
  go :: String -> [Token]
  go [] = []
  go (c:s) = go1 c s id
  go1 :: Char -> String -> (String -> String) -> [Token]
  go1 c s f | S.member c ds = case f [] of
    [] -> [c] : go s
    s1 -> s1 : [c] : go s
  go1 c [] f = [f [c]]
  go1 c (c':s) f = go1 c' s (f . (c:))

tokenize1 :: ParserEnv -> Const -> Either String Token
tokenize1 env cnst = case tokenize env cnst of
  [tk] -> return tk
  tks -> throwError ("bad token" ++ show tks)

checkToken :: ParserEnv -> Token -> Bool
checkToken _ [c] = c `notElem` " \t\r\n"
checkToken e tk = all ok tk where
  ok c = c `S.notMember` delims e && c `notElem` " \t\r\n"

identCh1 :: Char -> Bool
identCh1 c = 'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' || c == '_' || c == '-'

identCh :: Char -> Bool
identCh c = '0' <= c && c <= '9' || identCh1 c

identStr :: String -> Bool
identStr [] = False
identStr (c:s) = identCh1 c && all identCh s

mkLiterals :: Int -> Prec -> Int -> [PLiteral]
mkLiterals 0 _ _ = []
mkLiterals 1 p n = [PVar n p]
mkLiterals i p n = PVar n maxBound : mkLiterals (i-1) p (n+1)

insertPrec :: Token -> Prec -> ParserEnv -> Either String ParserEnv
insertPrec tk p e = do
  guardError ("incompatible precedence for " ++ tk)
    (maybe True (p ==) (prec e M.!? tk))
  return (e {prec = M.insert tk p (prec e)})

insertPrefixInfo :: Token -> PrefixInfo -> ParserEnv -> Either String ParserEnv
insertPrefixInfo tk ti e = do
  guardError ("invalid token '" ++ tk ++ "'") (checkToken e tk)
  ts <- insertNew ("token '" ++ tk ++ "' already declared") tk ti (prefixes e)
  return (e {prefixes = ts})

insertInfixInfo :: Token -> InfixInfo -> ParserEnv -> Either String ParserEnv
insertInfixInfo tk ti e = do
  guardError ("invalid token '" ++ tk ++ "'") (checkToken e tk)
  ts <- insertNew ("token '" ++ tk ++ "' already declared") tk ti (infixes e)
  return (e {infixes = ts})

matchBinders :: [Binder] -> DepType -> ([PBinder], DepType) -> Bool
matchBinders bs' r' (bs, r) = go bs bs' where
  go :: [PBinder] -> [Binder] -> Bool
  go [] [] = r == r'
  go (PBound b t : bs) (Binder (LBound b') (TType (DepType t' [])) : bs') =
    b == b' && t == t' && go bs bs'
  go (PReg b ty : bs) (Binder (LReg b') (TType ty') : bs') =
    b == b' && ty == ty' && go bs bs'
  go _ _ = False

processLits :: [Binder] -> [Literal] -> StateT ParserEnv (Either String) (Token, [PLiteral])
processLits bis (NConst c p : lits) = liftM2 (,) (processConst c p) (go lits) where
  processConst :: Const -> Prec -> StateT ParserEnv (Either String) Token
  processConst c p = StateT $ \e -> do
    tk <- tokenize1 e c
    e' <- insertPrec tk p e
    return (tk, e')
  go :: [Literal] -> StateT ParserEnv (Either String) [PLiteral]
  go [] = return []
  go (NConst c' q : lits) = liftM2 (:) (PConst <$> processConst c' q) (go lits)
  go (NVar v : lits) = do
    q <- case lits of
      [] -> return p
      (NConst _ q : _) -> do
        guardError "notation infix prec max not allowed" (q < maxBound)
        return (q + 1)
      (NVar _ : _) -> return maxBound
    n <- lift $ lookup v
    (PVar n q :) <$> go lits
  lookup :: Ident -> Either String Int
  lookup v = fromJustError "notation variable not found" $
    findIndex (\(Binder l _) -> localName l == Just v) bis
processLits _ _ = throwError "notation must begin with a constant"

getCoe :: Ident -> Ident -> ParserEnv -> Maybe Coe
getCoe s1 s2 e | s1 == s2 = Just id
getCoe s1 s2 e = coes e M.!? s1 >>= (M.!? s2)

foldCoeLeft :: Ident -> ParserEnv -> (Ident -> Coe -> a -> a) -> a -> a
foldCoeLeft s2 e f a = M.foldrWithKey' g a (coes e) where
  g s1 m a = maybe a (\l -> f s1 l a) (m M.!? s2)

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
  e <- foldCoeLeft s1 e (\s1' l r -> r >>= addCoeInner s1' s2 (cc . l)) (return e)
  e <- addCoeInner s1 s2 cc e
  foldCoeRight s2 e (\s2' l r -> r >>= addCoeInner s1 s2' (l . cc)) (return e)

addNotation :: Notation -> Environment -> ParserEnv -> Either String ParserEnv
addNotation (Delimiter s) _ e = do
  ds' <- go (splitOneOf " \t\r\n" (toString s)) (delims e)
  return (e {delims = ds'}) where
    go :: [String] -> S.Set Char -> Either String (S.Set Char)
    go [] s = return s
    go ([]:ds) s = go ds s
    go ([c]:ds) s = go ds (S.insert c s)
    go (_:_) _ = throwError "multiple char delimiters not supported"
addNotation (Prefix x s prec) env e = do
  n <- fromJustError ("term " ++ x ++ " not declared") (getArity env x)
  tk <- tokenize1 e s
  e' <- insertPrec tk prec e
  insertPrefixInfo tk (PrefixInfo x (mkLiterals n prec 0)) e'
addNotation (Infix r x s prec) env e = do
  n <- fromJustError ("term " ++ x ++ " not declared") (getArity env x)
  guardError ("'" ++ x ++ "' must be a binary operator") (n == 2)
  guardError "infix prec max not allowed" (prec < maxBound)
  tk <- tokenize1 e s
  e' <- insertPrec tk prec e
  insertInfixInfo tk (InfixInfo x r) e'
addNotation (NNotation x bi ty lits) env e = do
  ty' <- fromJustError ("term " ++ x ++ " not declared") (getTerm env x)
  guardError ("notation declaration for '" ++ x ++ "' must match term") (matchBinders bi ty ty')
  ((tk, ti), e') <- runStateT (processLits bi lits) e
  insertPrefixInfo tk (PrefixInfo x ti) e'
addNotation (Coercion x s1 s2) env e = do
  fromJustError ("term " ++ x ++ " not declared") (getTerm env x) >>= \case
    ([PReg _ (DepType s1' [])], DepType s2' []) | s1 == s1' && s2 == s2' ->
      addCoe s1 s2 x e
    _ -> throwError ("coercion '" ++ x ++ "' does not match declaration")
