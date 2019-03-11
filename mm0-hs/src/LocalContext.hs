module LocalContext where

import Control.Applicative
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State (StateT, runStateT)
import Control.Monad.State.Class
import Control.Monad.Except
import Data.Maybe
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import AST
import Environment
import ParserEnv
import Util

data Locals = Locals {
  lBound :: S.Set Ident,
  lNewVars :: S.Set Ident }

type LCtx = ([PBinder], M.Map Ident Ident)

lookupReg :: [PBinder] -> Ident -> Maybe DepType
lookupReg [] _ = Nothing
lookupReg (PBound v' t : bs) v | v == v' = Just (DepType t [])
lookupReg (PReg v' ty : bs) v | v == v' = Just ty
lookupReg (b : bs) v = lookupReg bs v

lookupLocal :: LCtx -> Ident -> Maybe DepType
lookupLocal (bs, ds) v = ((\t -> DepType t []) <$> ds M.!? v) <|> lookupReg bs v

lcRegCons :: PBinder -> LCtx -> Either String LCtx
lcRegCons b (bs, ds) = do
  guardError "dummy and regular variables have same name" $ M.notMember (binderName b) ds
  return (b:bs, ds)

lcDummyCons :: Ident -> Ident -> LCtx -> Either String LCtx
lcDummyCons d t (bs, ds) = do
  guardError "dummy and regular variables have same name" $ isNothing (lookupReg bs d)
  return (bs, M.insert d t ds)

type LocalCtxM = ReaderT LCtx
  (ReaderT (Stack, (Environment, ParserEnv))
    (StateT Locals (Either String)))

runLocalCtxM :: LocalCtxM a -> Stack -> (Environment, ParserEnv) -> Either String (a, Locals)
runLocalCtxM m s e = runStateT (runReaderT (runReaderT m ([], M.empty)) (s, e)) (Locals S.empty S.empty)

lcmLocal :: (LCtx -> Either String LCtx) -> LocalCtxM a -> LocalCtxM a
lcmLocal f m = ReaderT $ \ctx -> lift (lift (f ctx)) >>= runReaderT m

readStack :: LocalCtxM Stack
readStack = fst <$> lift ask

readEnv :: LocalCtxM Environment
readEnv = fst . snd <$> lift ask

readPE :: LocalCtxM ParserEnv
readPE = snd . snd <$> lift ask

lookupVarSort :: Stack -> LCtx -> Ident -> Maybe (Ident, Bool)
lookupVarSort stk ctx v =
  case lookupLocal ctx v of
    Just (DepType s _) -> Just (s, True)
    Nothing -> (\t -> (varTypeSort t, False)) <$> sVars stk M.!? v

makeBound :: Ident -> LocalCtxM ()
makeBound v = modify (\loc -> loc {lBound = S.insert v (lBound loc)})

insertLocal :: Ident -> LocalCtxM ()
insertLocal v = modify (\loc -> loc {lNewVars = S.insert v (lNewVars loc)})

ensureLocal :: Ident -> LocalCtxM ()
ensureLocal v = do
  ctx <- ask
  Locals bd nv <- get
  when (isNothing (lookupLocal ctx v)) $
    put (Locals bd (S.insert v nv))
