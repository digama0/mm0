module CEnv (module CEnv, Offset, SortData, Visibility,
  Ident, Sort, TermName, ThmName, VarName, Token,
  Binder, DepType(..), PBinder(..), SExpr(..), binderName, binderType,
  LispVal, Prec) where

import Control.Concurrent.STM
import Control.Concurrent.STM.TVar
import Data.Maybe
import Control.Monad.Trans.Maybe
import Control.Monad.RWS.Strict
import Data.List
import Data.Word8
import qualified Data.Text as T
import Data.Text (Text)
import Data.Default
import qualified Data.Set as S
import qualified Data.IntMap as I
import qualified Data.Map.Strict as M
import qualified Data.HashMap.Strict as H
import qualified Data.HashSet as HS
import qualified Data.Vector.Mutable.Dynamic as V
import qualified Data.Vector.Unboxed as U
import CAST
import Environment (Ident, Sort, TermName, ThmName, VarName, Token,
  PBinder(..), SExpr(..), DepType(..), binderName, binderType)
import Text.Megaparsec (errorOffset, parseErrorTextPretty)
import CParser (ParseError)

data ErrorLevel = ELError | ELWarning | ELInfo
data ElabError = ElabError {
  eeLevel :: ErrorLevel,
  eeBegin :: Offset,
  eeEnd :: Offset,
  eeMsg :: Text,
  eeRelated :: [(Offset, Offset, Text)] }

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

data PLiteral = PConst Text | PVar Int Prec deriving (Show)

data PrefixInfo = PrefixInfo Offset Text [PLiteral] deriving (Show)
data InfixInfo = InfixInfo Offset Text Bool deriving (Show)
data Coe1 = Coe1 Offset Text
data Coe = Coe Coe1 | Coes Coe Text Coe

appCoe1 :: Coe1 -> LispVal -> LispVal
appCoe1 (Coe1 _ t) e = List [Atom t, e]

appCoe :: Coe -> LispVal -> LispVal
appCoe (Coe c) = appCoe1 c
appCoe (Coes c1 _ c2) = appCoe c1 . appCoe c2

coeToList :: Coe -> Ident -> Ident -> [(Coe1, Ident, Ident)]
coeToList c s1 s2 = go c s1 s2 [] where
  go :: Coe -> Ident -> Ident -> [(Coe1, Ident, Ident)] -> [(Coe1, Ident, Ident)]
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
  | DDef Visibility [PBinder] DepType SExpr
  | DTheorem Visibility [PBinder] [SExpr] SExpr LispVal

data LocalInfer = LIOld Binder (Maybe Text) | LINew Offset Bool Text

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

runElab :: Elab a -> [ElabError] -> IO (a, Env, [ElabError])
runElab m errs = do
  pErrs <- newTVarIO errs
  let report e = atomically $ modifyTVar pErrs (e :)
  dat <- V.unsafeNew 16
  (a, env, _) <- runRWST m report def {eLispData = dat}
  errs <- readTVarIO pErrs
  return (a, env, errs)

resuming :: ElabM () -> Elab ()
resuming m = () <$ runMaybeT m

reportErr :: ElabError -> ElabM ()
reportErr e = lift $ ask >>= \f -> lift $ f e

reportAt :: Offset -> ErrorLevel -> Text -> ElabM ()
reportAt o l s = reportErr $ ElabError l o o s []

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

getSort :: Text -> SeqNum -> ElabM (Offset, SortData)
getSort v s =
  gets (H.lookup v . eSorts) >>= \case
    Just (n, o, sd) -> guard (n < s) >> return (o, sd)
    _ -> mzero

getTerm :: Text -> SeqNum -> ElabM (Offset, [PBinder], DepType)
getTerm v s =
  gets (H.lookup v . eDecls) >>= \case
    Just (n, o, DTerm args r) -> guard (n < s) >> return (o, args, r)
    Just (n, o, DDef _ args r _) -> guard (n < s) >> return (o, args, r)
    _ -> mzero

getThm :: Text -> SeqNum -> ElabM (Offset, [PBinder], [SExpr], SExpr)
getThm v s =
  gets (H.lookup v . eDecls) >>= \case
    Just (n, o, DAxiom args hyps r) -> guard (n < s) >> return (o, args, hyps, r)
    Just (n, o, DTheorem _ args hyps r _) -> guard (n < s) >> return (o, args, hyps, r)
    _ -> mzero

modifyInfer :: (InferCtx -> InferCtx) -> Elab ()
modifyInfer f = modify $ \env -> env {eInfer = f (eInfer env)}

withInfer :: ElabM () -> ElabM ()
withInfer m =
  lift (modifyInfer (const def)) >> m >>
  lift (modifyInfer (const undefined))

lookupOrInferLocal :: Text -> Text -> Offset -> ElabM Text
lookupOrInferLocal v s o =
  gets (H.lookup v . icLocals . eInfer) >>= \case
    Nothing -> do
      lift $ modifyInfer $ \ic -> ic {
        icLocals = H.insert v (LINew o False s) (icLocals ic)}
      undefined

getCoe' :: Text -> Text -> ElabM Coe
getCoe' s1 s2 = do
  mm <- gets (pCoes . ePE)
  fromJust' $ M.lookup s1 mm >>= M.lookup s2

getCoe :: Text -> Text -> ElabM (LispVal -> LispVal)
getCoe s1 s2 | s1 == s2 = return id
getCoe s1 s2 = appCoe <$> getCoe' s1 s2

getCoeProv :: Text -> ElabM (Text, LispVal -> LispVal)
getCoeProv s = do
  s2 <- gets (H.lookup s . pCoeProv . ePE) >>= fromJust'
  c <- getCoe s s2
  return (s2, c)

addCoe :: Coe1 -> Sort -> Sort -> ElabM ()
addCoe cc@(Coe1 o c) s1 s2 = do
  let cs = Coe cc
  coes <- gets (pCoes . ePE)
  coes <- foldCoeLeft s1 coes (\s1' l r -> r >>= addCoeInner o (Coes cs s1' l) s1' s2) (return coes)
  coes <- addCoeInner o cs s1 s2 coes
  coes <- foldCoeRight s2 coes (\s2' l r -> r >>= addCoeInner o (Coes l s2' cs) s1 s2') (return coes)
  setCoes coes
  where

  foldCoeLeft :: Sort -> M.Map Sort (M.Map Sort Coe) -> (Sort -> Coe -> a -> a) -> a -> a
  foldCoeLeft s2 coes f a = M.foldrWithKey' g a coes where
    g s1 m a = maybe a (\l -> f s1 l a) (M.lookup s2 m)

  foldCoeRight :: Sort -> M.Map Sort (M.Map Sort Coe) -> (Sort -> Coe -> a -> a) -> a -> a
  foldCoeRight s1 coes f a = maybe a (M.foldrWithKey' f a) (M.lookup s1 coes)

  toStrs :: [(Coe1, Sort, Sort)] -> [Text]
  toStrs [(c, s1, s2)] = [s1, " -> ", s2]
  toStrs ((c, s1, s2) : cs) = s1 : " -> " : toStrs cs

  toRelated :: [(Coe1, Sort, Sort)] -> [(Offset, Offset, Text)]
  toRelated = fmap $ \(Coe1 o x, s1, s2) -> (o, o, s1 <> " -> " <> s2)

  addCoeInner :: Offset -> Coe -> Sort -> Sort ->
    M.Map Sort (M.Map Sort Coe) -> ElabM (M.Map Sort (M.Map Sort Coe))
  addCoeInner o c s1 s2 coes = do
    let l = coeToList c s1 s2
    when (s1 == s2) $ do
      reportErr $ ElabError ELError o o
        (T.concat ("coercion cycle detected: " : toStrs l))
        (toRelated l)
      mzero
    try (getCoe' s1 s2) >>= mapM_ (\c2 -> do
      let l2 = coeToList c2 s1 s2
      reportErr $ ElabError ELError o o
        (T.concat ("coercion diamond detected: " : toStrs l ++ ";   " : toStrs l2))
        (toRelated (l ++ l2))
      mzero)
    return $ M.alter (Just . M.insert s2 c . maybe M.empty id) s1 coes

  setCoes :: M.Map Sort (M.Map Sort Coe) -> ElabM ()
  setCoes coes = do
    sorts <- gets eSorts
    let provs = H.keysSet (H.filter (\(_, _, sd) -> sProvable sd) sorts)
        f :: Sort -> Sort -> Coe -> ElabM (H.HashMap Sort Sort) -> ElabM (H.HashMap Sort Sort)
        f s1 s2 c2 r =
          if HS.member s2 provs then do
            m <- r
            forM_ (H.lookup s1 m) $ \s2 -> do
              c1 <- getCoe' s1 s2
              let l1 = coeToList c1 s1 s2
              let l2 = coeToList c2 s1 s2
              reportErr $ ElabError ELError o o
                (T.concat ("coercion diamond to provable detected:\n" :
                  toStrs l1 ++ " provable\n" : toStrs l2 ++ [" provable"]))
                (toRelated (l1 ++ l2))
              mzero
            return (H.insert s1 s2 m)
          else r
    m <- M.foldrWithKey' (\s1 m r -> M.foldrWithKey' (f s1) r m)
      (return (foldr (\v -> H.insert v v) H.empty provs)) coes
    lift $ modifyPE $ \pe -> pe {pCoes = coes, pCoeProv = m}
