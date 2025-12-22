module MM0.FrontEnd.LocalContext where

import Control.Monad (void)
import Control.Monad.Trans.Class
import Control.Applicative
import Control.Monad.Trans.Reader
import Data.Maybe
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import MM0.FrontEnd.AST
import MM0.Kernel.Environment
import MM0.FrontEnd.ParserEnv
import MM0.Util

type LCtx = ([PBinder], M.Map Ident Ident)

lookupReg :: [PBinder] -> Ident -> Maybe DepType
lookupReg [] _ = Nothing
lookupReg (PBound v' t : _) v | v == v' = Just (DepType t [])
lookupReg (PReg v' ty : _) v | v == v' = Just ty
lookupReg (_ : bs) v = lookupReg bs v

lookupLocal :: LCtx -> Ident -> Maybe DepType
lookupLocal (bs, ds) v = ((`DepType` []) <$> ds M.!? v) <|> lookupReg bs v

lookupBound :: LCtx -> Ident -> Maybe Ident
lookupBound (bs, ds) v = ds M.!? v <|> lookupBound' bs where
  lookupBound' [] = Nothing
  lookupBound' (PBound v' t : _) | v == v' = Just t
  lookupBound' (_ : bs') = lookupBound' bs'

lcRegCons :: PBinder -> LCtx -> Either String LCtx
lcRegCons b (bs, ds) = do
  guardError "dummy and regular variables have same name" $ M.notMember (binderName b) ds
  return (b:bs, ds)

lcDummyCons :: Ident -> Ident -> LCtx -> Either String LCtx
lcDummyCons d t (bs, ds) = do
  guardError "dummy and regular variables have same name" $ isNothing (lookupReg bs d)
  return (bs, M.insert d t ds)

type LocalCtxM = ReaderT LCtx (ReaderT (Environment, ParserEnv) (Either String))

runLocalCtxM :: LocalCtxM a -> (Environment, ParserEnv) -> Either String a
runLocalCtxM m = runReaderT (runReaderT m ([], M.empty))

lcmLocal :: (LCtx -> Either String LCtx) -> LocalCtxM a -> LocalCtxM a
lcmLocal f m = ReaderT $ \ctx -> lift (f ctx) >>= runReaderT m

readEnv :: LocalCtxM Environment
readEnv = fst <$> lift ask

readPE :: LocalCtxM ParserEnv
readPE = snd <$> lift ask

ensureBound :: Ident -> LocalCtxM ()
ensureBound v = do
  ctx <- ask
  void $ fromJustError ("variable " ++ T.unpack v ++ " not bound") (lookupBound ctx v)
