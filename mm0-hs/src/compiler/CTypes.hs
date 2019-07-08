module CTypes (module CTypes, Offset, SortData, Visibility,
  Binder, DepType, LispVal, Prec) where

import Control.Concurrent.STM
import Control.Concurrent.STM.TVar
import Data.Maybe
import Control.Monad.Trans.Maybe
import Control.Monad.RWS.Strict
import Data.List
import Data.Text (Text)
import Data.Default
import qualified Data.Set as S
import qualified Data.IntMap as I
import qualified Data.Map.Strict as M
import qualified Data.HashMap.Strict as H
import CAST

data ErrorLevel = ELError | ELWarning | ELInfo
data ElabError = ElabError {
  eeLevel :: ErrorLevel,
  eeBegin :: Offset,
  eeEnd :: Offset,
  eeMsg :: Text,
  eeRelated :: [(Offset, Offset, Text)] }

-- This represents a hierarchical ordering of values:
-- 1 < 1.1.1 < 1.2 < 2 < 3
-- All sequence numbers are strictly positive.
data SeqNum = Simple Int | After Int SeqNum deriving (Eq)

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

data SeqCounter = SeqCounter (I.IntMap SeqCounter) Int

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
type Coe = LispVal -> LispVal

data ParserEnv = ParserEnv {
  pDelims :: S.Set Char,
  pPrefixes :: H.HashMap Text PrefixInfo,
  pInfixes :: H.HashMap Text InfixInfo,
  pPrec :: H.HashMap Text (Offset, Prec),
  pCoes :: H.HashMap Text (H.HashMap Text Coe),
  pCoeProv :: H.HashMap Text Text }

instance Default ParserEnv where
  def = ParserEnv def H.empty H.empty H.empty H.empty H.empty

data Decl =
    DTerm [Binder] DepType
  | DAxiom [Binder] LispVal
  | DDef Visibility [Binder] DepType LispVal
  | DTheorem Visibility [Binder] LispVal LispVal

data LocalInfer = LIOld (Maybe Text) | LINew
data InferCtx = InferCtx {
  icDependents :: H.HashMap Text [Offset],
  icLocals :: H.HashMap Text (Binder, LocalInfer) }

instance Default InferCtx where
  def = InferCtx H.empty H.empty

data Env = Env {
  eHere :: Offset,
  eLispCtx :: H.HashMap Text LispVal,
  eCounter :: SeqCounter,
  eSorts :: H.HashMap Text (SeqNum, Offset, SortData),
  eDecls :: H.HashMap Text (SeqNum, Offset, Decl),
  ePE :: ParserEnv,
  eInfer :: InferCtx }

instance Default Env where
  def = Env def H.empty def H.empty H.empty def undefined

type Elab = RWST (ElabError -> IO ()) () Env IO
type ElabM = MaybeT Elab

runElab :: Elab a -> [ElabError] -> IO (a, Env, [ElabError])
runElab m errs = do
  pErrs <- newTVarIO errs
  let report e = atomically $ modifyTVar pErrs (e :)
  (a, env, _) <- runRWST m report def
  errs <- readTVarIO pErrs
  return (a, env, errs)

resuming :: ElabM () -> Elab ()
resuming m = () <$ runMaybeT m

reportErr :: ElabError -> ElabM ()
reportErr e = lift $ ask >>= \f -> lift $ f e

reportAt :: Offset -> ErrorLevel -> Text -> ElabM ()
reportAt o l s = reportErr $ ElabError l o o s []

report :: ErrorLevel -> Text -> ElabM ()
report l s = get >>= \env -> reportAt (eHere env) l s

escapeAt :: Offset -> Text -> ElabM a
escapeAt o s = reportAt o ELError s >> mzero

escape :: Text -> ElabM a
escape s = report ELError s >> mzero

unwrap :: ElabM a -> Elab a
unwrap m = fromJust <$> runMaybeT m

fromJustAt :: Offset -> Text -> Maybe a -> ElabM a
fromJustAt _ _ (Just a) = return a
fromJustAt o msg Nothing = escapeAt o msg

guardAt :: Offset -> Text -> Bool -> ElabM ()
guardAt _ _ True = return ()
guardAt o msg False = escapeAt o msg

putHere :: Offset -> Elab ()
putHere o = modify $ \env -> env {eHere = o}

modifyPE :: (ParserEnv -> ParserEnv) -> Elab ()
modifyPE f = modify $ \env -> env {ePE = f (ePE env)}

after :: Maybe SeqNum -> ElabM SeqNum
after s = MaybeT $ state $ \env ->
  case incCounter s (eCounter env) of
    Nothing -> (Nothing, env)
    Just (n, c') -> (Just (snFold n s), env {eCounter = c'})

next :: ElabM SeqNum
next = after Nothing

try :: ElabM a -> ElabM (Maybe a)
try = lift . runMaybeT

getTerm :: Text -> ElabM (Offset, [Binder], DepType)
getTerm v = do
  env <- get
  case H.lookup v (eDecls env) of
    Just (_, o, DTerm args r) -> return (o, args, r)
    Just (_, o, DDef _ args r _) -> return (o, args, r)
    _ -> mzero

getThm :: Text -> ElabM (Offset, [Binder], LispVal)
getThm v = do
  env <- get
  case H.lookup v (eDecls env) of
    Just (n, o, DAxiom args r) -> return (o, args, r)
    Just (n, o, DTheorem _ args r _) -> return (o, args, r)
    _ -> mzero

modifyInfer :: (InferCtx -> InferCtx) -> Elab ()
modifyInfer f = modify $ \env -> env {eInfer = f (eInfer env)}

withInfer :: ElabM () -> ElabM ()
withInfer m =
  lift (modifyInfer (const def)) >> m >>
  lift (modifyInfer (const undefined))
