module MM0.FrontEnd.ParserEnv (Token,
  PLiteral(..),
  ParserEnv(..),
  PrefixInfo(..),
  InfixInfo(..),
  addNotation, recalcCoeProv, tokenize, getCoe, getCoeProv) where

import Control.Monad.Except
import Control.Monad.Trans.State
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

data PrefixInfo = PrefixInfo Ident [PLiteral] deriving (Show)
data InfixInfo = InfixInfo Ident Bool deriving (Show)
type Coe = SExpr -> SExpr

data ParserEnv = ParserEnv {
  delims :: S.Set Char,
  prefixes :: M.Map Token PrefixInfo,
  infixes :: M.Map Token InfixInfo,
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

insertPrefixInfo :: Token -> PrefixInfo -> ParserEnv -> Either String ParserEnv
insertPrefixInfo tk ti e = do
  guardError ("invalid token '" ++ T.unpack tk ++ "'") (checkToken e tk)
  ts <- insertNew ("token '" ++ T.unpack tk ++ "' already declared") tk ti (prefixes e)
  return (e {prefixes = ts})

insertInfixInfo :: Token -> InfixInfo -> ParserEnv -> Either String ParserEnv
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

processLits :: [Binder] -> [Literal] -> StateT ParserEnv (Either String) (Token, [PLiteral])
processLits bis (NConst c p : lits') = liftM2 (,) (processConst c p) (go lits') where
  processConst :: Const -> Prec -> StateT ParserEnv (Either String) Token
  processConst c' p' = StateT $ \e -> do
    tk <- tokenize1 e c'
    e' <- insertPrec tk p' e
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
    n <- lift $ findVar v
    (PVar n q :) <$> go lits
  findVar :: Ident -> Either String Int
  findVar v = fromJustError "notation variable not found" $
    findIndex (\(Binder l _) -> localName l == Just v) bis
processLits _ _ = throwError "notation must begin with a constant"

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
  insertPrefixInfo tk (PrefixInfo x (mkLiterals n p 0)) e'
addNotation (Infix r x s p) env e = do
  n <- fromJustError ("term " ++ T.unpack x ++ " not declared") (getArity env x)
  guardError ("'" ++ T.unpack x ++ "' must be a binary operator") (n == 2)
  guardError "infix prec max not allowed" (p < maxBound)
  tk <- tokenize1 e s
  e' <- insertPrec tk p e
  insertInfixInfo tk (InfixInfo x r) e'
addNotation (NNotation x bi ty lits) env e = do
  ty' <- fromJustError ("term " ++ T.unpack x ++ " not declared") (getTerm env x)
  guardError ("notation declaration for '" ++ T.unpack x ++ "' must match term") (matchBinders bi ty ty')
  ((tk, ti), e') <- runStateT (processLits bi lits) e
  insertPrefixInfo tk (PrefixInfo x ti) e'
addNotation (Coercion x s1 s2) env e = do
  fromJustError ("term " ++ T.unpack x ++ " not declared") (getTerm env x) >>= \case
    ([PReg _ (DepType s1' [])], DepType s2' []) | s1 == s1' && s2 == s2' ->
      addCoe s1 s2 x e >>= recalcCoeProv env
    _ -> throwError ("coercion '" ++ T.unpack x ++ "' does not match declaration")
