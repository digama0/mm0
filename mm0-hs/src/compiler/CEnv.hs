module CEnv (module CEnv, Offset, SortData, Visibility(..),
  Ident, Sort, TermName, ThmName, VarName, Token,
  Binder, DepType(..), PBinder(..), SExpr(..), binderName, binderType,
  Prec) where

import Control.Concurrent.STM
import Control.Concurrent
import Data.Maybe
import Control.Monad.Trans.Maybe
import Control.Monad.RWS.Strict
import Data.Word8
import qualified Data.Text as T
import Data.Text (Text)
import Data.Default
import qualified Data.IntMap as I
import qualified Data.Map.Strict as M
import qualified Data.HashMap.Strict as H
import qualified Data.HashSet as HS
import qualified Data.Vector.Mutable.Dynamic as V
import qualified Data.Vector.Unboxed as U
import CAST (Offset, Binder(..), SortData(..), Prec, Visibility(..))
import Environment (Ident, Sort, TermName, ThmName, VarName, Token,
  PBinder(..), SExpr(..), DepType(..), binderName, binderType)
import Text.Megaparsec (errorOffset, parseErrorTextPretty)
import CParser (ParseError)

data Syntax = Define | Lambda | Quote | If

type Proc = Offset -> Offset -> [LispVal] -> ElabM LispVal

data LispVal =
    Atom (Maybe Offset) T.Text
  | List [LispVal]
  | DottedList LispVal [LispVal] LispVal
  | Number Integer
  | String T.Text
  | UnparsedFormula Offset T.Text
  | Bool Bool
  | Syntax Syntax
  | Undef
  | Proc Proc

instance Show LispVal where
  showsPrec _ (Atom _ e) = (T.unpack e ++)
  showsPrec _ (List [Syntax Quote, e]) = ('\'' :) . shows e
  showsPrec _ (List ls) = ('(' :) . f ls . (')' :) where
    f [] = id
    f [e] = shows e
    f (e : es) = shows e . (' ' :) . f es
  showsPrec _ (DottedList l ls e') =
    ('(' :) . flip (foldr (\e -> shows e . (' ' :))) (l : ls) .
    (". " ++) . shows e' . (')' :)
  showsPrec _ (Number n) = shows n
  showsPrec _ (String s) = shows s
  showsPrec _ (Bool True) = ("#t" ++)
  showsPrec _ (Bool False) = ("#f" ++)
  showsPrec _ (UnparsedFormula _ f) = ('$' :) . (T.unpack f ++) . ('$' :)
  showsPrec _ (Syntax Define) = ("#def" ++)
  showsPrec _ (Syntax Lambda) = ("#fn" ++)
  showsPrec _ (Syntax Quote) = ("#quote" ++)
  showsPrec _ (Syntax If) = ("#if" ++)
  showsPrec _ Undef = ("#<undef>" ++)
  showsPrec _ (Proc _) = ("#<closure>" ++)

cons :: LispVal -> LispVal -> LispVal
cons l (List r) = List (l : r)
cons l (DottedList r0 rs r) = DottedList l (r0 : rs) r
cons l r = DottedList l [] r

data ErrorLevel = ELError | ELWarning | ELInfo
instance Show ErrorLevel where
  show ELError = "error"
  show ELWarning = "warning"
  show ELInfo = "info"

data ElabError = ElabError {
  eeLevel :: ErrorLevel,
  eeBegin :: Offset,
  eeEnd :: Offset,
  eeMsg :: Text,
  eeRelated :: [(Offset, Offset, Text)] } deriving (Show)

toElabError :: ParseError -> ElabError
toElabError e = ElabError ELError (errorOffset e) (errorOffset e)
  (T.pack (parseErrorTextPretty e)) []

-- This represents a hierarchical ordering of values:
-- 1 < 1.1 < 1.1.1 < 1.2 < 2 < 3
-- All sequence numbers are strictly positive.
data SeqNum = Simple Int | After Int SeqNum deriving (Eq)

instance Show SeqNum where
  showsPrec _ (Simple n) = shows n
  showsPrec _ (After n s) = shows n . ('.' :) . shows s

snUnfold :: SeqNum -> (Int, Maybe SeqNum)
snUnfold (Simple m) = (m, Nothing)
snUnfold (After m s) = (m, Just s)

snFold :: Int -> Maybe SeqNum -> SeqNum
snFold n = maybe (Simple n) (After n)

instance Ord SeqNum where
  compare (Simple m) (Simple n) = compare m n
  compare (Simple m) (After n _) = compare m n <> LT
  compare (After m _) (Simple n) = compare m n <> GT
  compare (After m s) (After n t) = compare m n <> compare s t

data SeqCounter = SeqCounter (I.IntMap SeqCounter) Int deriving (Show)

instance Default SeqCounter where
  def = SeqCounter def 1

incCounter :: Maybe SeqNum -> SeqCounter -> Maybe (Int, SeqCounter)
incCounter Nothing (SeqCounter c n) = Just (n, SeqCounter c (n+1))
incCounter (Just s) (SeqCounter c n) = do
  let (m, s') = snUnfold s
  (i, c'') <- case c I.!? m of
    Nothing -> return (1, def)
    Just c' -> incCounter s' c'
  return (i, SeqCounter (I.insert m c'' c) n)

data PLiteral = PConst Token | PVar Int Prec deriving (Show)

data PrefixInfo = PrefixInfo Offset Token [PLiteral] deriving (Show)
data InfixInfo = InfixInfo Offset Token Bool deriving (Show)
data Coe1 = Coe1 Offset Sort
data Coe = Coe Coe1 | Coes Coe Sort Coe

foldCoe :: (Text -> a -> a) -> Coe -> a -> a
foldCoe tm (Coe (Coe1 _ t)) = tm t
foldCoe tm (Coes c1 _ c2) = foldCoe tm c1 . foldCoe tm c2

coeToList :: Coe -> Sort -> Sort -> [(Coe1, Sort, Sort)]
coeToList c' s1' s2' = go c' s1' s2' [] where
  go :: Coe -> Sort -> Sort -> [(Coe1, Sort, Sort)] -> [(Coe1, Sort, Sort)]
  go (Coe c) s1 s2 = ((c, s1, s2) :)
  go (Coes g s2 f) s1 s3 = go g s2 s3 . go f s1 s2

newtype Delims = Delims (U.Vector Word8)

instance Default Delims where
  def = Delims $ U.replicate 256 0 U.// [(fromEnum '\n', 4), (fromEnum ' ', 4)]

delimVal :: Delims -> Char -> Word8
delimVal (Delims v) c = U.unsafeIndex v (fromEnum (toEnum (fromEnum c) :: Word8))

data ParserEnv = ParserEnv {
  pDelims :: Delims,
  pPrefixes :: H.HashMap Token PrefixInfo,
  pInfixes :: H.HashMap Token InfixInfo,
  pPrec :: H.HashMap Token (Offset, Prec),
  pCoes :: M.Map Sort (M.Map Sort Coe),
  pCoeProv :: H.HashMap Sort Sort }

instance Default ParserEnv where
  def = ParserEnv def H.empty H.empty H.empty def H.empty

data Decl =
    DTerm [PBinder] DepType
  | DAxiom [PBinder] [SExpr] SExpr
  | DDef Visibility [PBinder] DepType [(Offset, VarName, Sort)] SExpr
  | DTheorem Visibility [PBinder] [SExpr] SExpr (ElabM LispVal)

data LocalInfer = LIOld Binder (Maybe Sort) | LINew Offset Bool Sort

liOffset :: LocalInfer -> Offset
liOffset (LIOld (Binder o _ _) _) = o
liOffset (LINew o _ _) = o

data InferCtx = InferCtx {
  icDependents :: H.HashMap VarName [Offset],
  icLocals :: H.HashMap VarName LocalInfer }

instance Default InferCtx where
  def = InferCtx H.empty H.empty

data Env = Env {
  eLispData :: V.IOVector LispVal,
  eLispNames :: H.HashMap Ident Int,
  eCounter :: SeqCounter,
  eSorts :: H.HashMap Sort (SeqNum, Offset, SortData),
  eProvableSorts :: [Sort],
  eDecls :: H.HashMap Ident (SeqNum, Offset, Decl),
  ePE :: ParserEnv,
  eInfer :: InferCtx }

instance Default Env where
  def = Env undefined H.empty def H.empty def H.empty def undefined

type Elab = RWST (ElabError -> IO ()) () Env IO
type ElabM = MaybeT Elab

runElab :: Elab a -> [ElabError] -> [(Ident, LispVal)] -> IO (a, Env, [ElabError])
runElab m errs lvs = do
  pErrs <- newTVarIO errs
  let report e = atomically $ modifyTVar pErrs (e :)
  dat <- V.new 0
  let ins :: [(Ident, LispVal)] -> Int -> H.HashMap Ident Int -> IO (H.HashMap Ident Int)
      ins [] _ hm = return hm
      ins ((x, v) : ls) n hm = V.pushBack dat v >> ins ls (n+1) (H.insert x n hm)
  hm <- ins lvs 0 H.empty
  (a, env, _) <- runRWST m report def {eLispData = dat, eLispNames = hm}
  errs' <- readTVarIO pErrs
  return (a, env, errs')

resuming :: ElabM () -> Elab ()
resuming m = () <$ runMaybeT m

reportErr :: ElabError -> ElabM ()
reportErr e = lift $ ask >>= \f -> lift $ f e

escapeErr :: ElabError -> ElabM a
escapeErr e = reportErr e >> mzero

reportAt :: Offset -> ErrorLevel -> Text -> ElabM ()
reportAt o l s = reportErr $ ElabError l o o s []

reportSpan :: Offset -> Offset -> ErrorLevel -> Text -> ElabM ()
reportSpan o1 o2 l s = reportErr $ ElabError l o1 o2 s []

escapeAt :: Offset -> Text -> ElabM a
escapeAt o s = reportAt o ELError s >> mzero

unimplementedAt :: Offset -> ElabM a
unimplementedAt pos = reportAt pos ELWarning "unimplemented" >> mzero

unwrap :: ElabM a -> Elab a
unwrap m = fromJust <$> runMaybeT m

fromJust' :: Maybe a -> ElabM a
fromJust' = MaybeT . return

fromJustAt :: Offset -> Text -> Maybe a -> ElabM a
fromJustAt _ _ (Just a) = return a
fromJustAt o msg Nothing = escapeAt o msg

guardAt :: Offset -> Text -> Bool -> ElabM ()
guardAt _ _ True = return ()
guardAt o msg False = escapeAt o msg

modifyPE :: (ParserEnv -> ParserEnv) -> Elab ()
modifyPE f = modify $ \env -> env {ePE = f (ePE env)}

after :: Maybe SeqNum -> ElabM SeqNum
after s = MaybeT $ state $ \env ->
  case incCounter s (eCounter env) of
    Nothing -> (Nothing, env)
    Just (n, c') -> (Just (snFold n s), env {eCounter = c'})

next :: ElabM SeqNum
next = after Nothing

now :: ElabM SeqNum
now = gets $ \env -> case eCounter env of SeqCounter _ n -> Simple n

try :: ElabM a -> ElabM (Maybe a)
try = lift . runMaybeT

forkElabM :: ElabM a -> ElabM (ElabM a)
forkElabM m = lift $ RWST $ \r s -> do
  v <- newEmptyMVar
  _ <- forkIO $ fst <$> evalRWST (runMaybeT m) r s >>= putMVar v
  return (MaybeT $ lift $ readMVar v, s, ())

lispAlloc :: LispVal -> ElabM Int
lispAlloc v = do
  vec <- gets eLispData
  liftIO $ V.length vec <* V.pushBack vec v

lispLookupNum :: Int -> ElabM LispVal
lispLookupNum n = do
  vec <- gets eLispData
  liftIO $ V.read vec n

lispLookupName :: T.Text -> ElabM LispVal
lispLookupName v = gets (H.lookup v . eLispNames) >>= \case
  Nothing -> mzero
  Just n -> lispLookupNum n

getSort :: Text -> SeqNum -> ElabM (Offset, SortData)
getSort v s =
  gets (H.lookup v . eSorts) >>= \case
    Just (n, o, sd) -> guard (n < s) >> return (o, sd)
    _ -> mzero

getTerm :: Text -> SeqNum -> ElabM (Offset, [PBinder], DepType)
getTerm v s =
  gets (H.lookup v . eDecls) >>= \case
    Just (n, o, DTerm args r) -> guard (n < s) >> return (o, args, r)
    Just (n, o, DDef _ args r _ _) -> guard (n < s) >> return (o, args, r)
    _ -> mzero

getThm :: Text -> SeqNum -> ElabM (Offset, [PBinder], [SExpr], SExpr)
getThm v s =
  gets (H.lookup v . eDecls) >>= \case
    Just (n, o, DAxiom args hyps r) -> guard (n < s) >> return (o, args, hyps, r)
    Just (n, o, DTheorem _ args hyps r _) -> guard (n < s) >> return (o, args, hyps, r)
    _ -> mzero

modifyInfer :: (InferCtx -> InferCtx) -> Elab ()
modifyInfer f = modify $ \env -> env {eInfer = f (eInfer env)}

withInfer :: ElabM a -> ElabM a
withInfer m =
  lift (modifyInfer (const def)) *> m <*
  lift (modifyInfer (const undefined))

peGetCoe' :: ParserEnv -> Text -> Text -> Maybe Coe
peGetCoe' pe s1 s2 = M.lookup s1 (pCoes pe) >>= M.lookup s2

getCoe' :: Text -> Text -> ElabM Coe
getCoe' s1 s2 = gets ePE >>= \pe -> fromJust' $ peGetCoe' pe s1 s2

peGetCoe :: ParserEnv -> (Text -> a -> a) -> Text -> Text -> Maybe (a -> a)
peGetCoe _ _ s1 s2 | s1 == s2 = return id
peGetCoe pe tm s1 s2 = foldCoe tm <$> peGetCoe' pe s1 s2

getCoe :: (Text -> a -> a) -> Text -> Text -> ElabM (a -> a)
getCoe tm s1 s2 = gets ePE >>= \pe -> fromJust' $ peGetCoe pe tm s1 s2

peGetCoeProv :: ParserEnv -> (Text -> a -> a) -> Text -> Maybe (Text, a -> a)
peGetCoeProv pe tm s = do
  s2 <- H.lookup s (pCoeProv pe)
  c <- peGetCoe pe tm s s2
  return (s2, c)

getCoeProv :: (Text -> a -> a) -> Text -> ElabM (Text, a -> a)
getCoeProv tm s = gets ePE >>= \pe -> fromJust' $ peGetCoeProv pe tm s

addCoe :: Coe1 -> Sort -> Sort -> ElabM ()
addCoe cc@(Coe1 o _) = \s1 s2 -> do
  let cs = Coe cc
  coes1 <- gets (pCoes . ePE)
  coes2 <- foldCoeLeft s1 coes1 (\s1' l r -> r >>= addCoeInner (Coes cs s1' l) s1' s2) (return coes1)
  coes3 <- addCoeInner cs s1 s2 coes2
  coes4 <- foldCoeRight s2 coes3 (\s2' l r -> r >>= addCoeInner (Coes l s2' cs) s1 s2') (return coes3)
  setCoes coes4
  where

  foldCoeLeft :: Sort -> M.Map Sort (M.Map Sort Coe) -> (Sort -> Coe -> a -> a) -> a -> a
  foldCoeLeft s2 coes f a' = M.foldrWithKey' g a' coes where
    g s1 m a = maybe a (\l -> f s1 l a) (M.lookup s2 m)

  foldCoeRight :: Sort -> M.Map Sort (M.Map Sort Coe) -> (Sort -> Coe -> a -> a) -> a -> a
  foldCoeRight s1 coes f a = maybe a (M.foldrWithKey' f a) (M.lookup s1 coes)

  toStrs :: [(Coe1, Sort, Sort)] -> [Text]
  toStrs [] = undefined
  toStrs [(_, s1, s2)] = [s1, " -> ", s2]
  toStrs ((_, s1, _) : cs) = s1 : " -> " : toStrs cs

  toRelated :: [(Coe1, Sort, Sort)] -> [(Offset, Offset, Text)]
  toRelated = fmap $ \(Coe1 o' _, s1, s2) -> (o', o', s1 <> " -> " <> s2)

  addCoeInner :: Coe -> Sort -> Sort ->
    M.Map Sort (M.Map Sort Coe) -> ElabM (M.Map Sort (M.Map Sort Coe))
  addCoeInner c s1 s2 coes = do
    let l = coeToList c s1 s2
    when (s1 == s2) $ do
      escapeErr $ ElabError ELError o o
        (T.concat ("coercion cycle detected: " : toStrs l))
        (toRelated l)
    try (getCoe' s1 s2) >>= mapM_ (\c2 -> do
      let l2 = coeToList c2 s1 s2
      escapeErr $ ElabError ELError o o
        (T.concat ("coercion diamond detected: " : toStrs l ++ ";   " : toStrs l2))
        (toRelated (l ++ l2)))
    return $ M.alter (Just . M.insert s2 c . maybe M.empty id) s1 coes

  setCoes :: M.Map Sort (M.Map Sort Coe) -> ElabM ()
  setCoes coes = do
    sorts <- gets eSorts
    let provs = H.keysSet (H.filter (\(_, _, sd) -> sProvable sd) sorts)
        f :: Sort -> Sort -> Coe -> ElabM (H.HashMap Sort Sort) -> ElabM (H.HashMap Sort Sort)
        f s1 s2' c' r =
          if HS.member s2' provs then do
            m <- r
            forM_ (H.lookup s1 m) $ \s2 -> do
              c <- getCoe' s1 s2
              let l = coeToList c s1 s2
              let l' = coeToList c' s1 s2'
              escapeErr $ ElabError ELError o o
                (T.concat ("coercion diamond to provable detected:\n" :
                  toStrs l ++ " provable\n" : toStrs l' ++ [" provable"]))
                (toRelated (l ++ l'))
            return (H.insert s1 s2' m)
          else r
    m <- M.foldrWithKey' (\s1' m r -> M.foldrWithKey' (f s1') r m)
      (return (foldr (\v -> H.insert v v) H.empty provs)) coes
    lift $ modifyPE $ \pe -> pe {pCoes = coes, pCoeProv = m}
