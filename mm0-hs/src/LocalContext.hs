module LocalContext where

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

data PType = PType Ident [Ident] | PFormula SExpr
data PBinder = PBinder Local PType

instance Show PType where
  showsPrec n (PType t ts) = showsPrec n (DepType t ts)
  showsPrec n (PFormula e) = showsPrec n e

instance Show PBinder where
  showsPrec n (PBinder l ty) = showsPrec n l . (": " ++) . showsPrec n ty

data Locals = Locals {
  lBound :: S.Set Ident,
  lNewVars :: S.Set Ident }

type LCtx = [PBinder]
type LocalCtxM = ReaderT LCtx
  (ReaderT (Stack, (Environment, ParserEnv))
    (StateT Locals (Either String)))

runLocalCtxM :: LocalCtxM a -> Stack -> (Environment, ParserEnv) -> Either String (a, Locals)
runLocalCtxM m s e = runStateT (runReaderT (runReaderT m []) (s, e)) (Locals S.empty S.empty)

readStack :: LocalCtxM Stack
readStack = fst <$> lift ask

readEnv :: LocalCtxM Environment
readEnv = fst . snd <$> lift ask

readPE :: LocalCtxM ParserEnv
readPE = snd . snd <$> lift ask

lookupLocal :: LCtx -> Ident -> Maybe PType
lookupLocal [] _ = Nothing
lookupLocal (PBinder l ty : ls) v =
  if localName l == Just v then Just ty else lookupLocal ls v

lookupVarSort :: Stack -> LCtx -> Ident -> Maybe (Ident, Bool)
lookupVarSort stk ctx v =
  case lookupLocal ctx v of
    Just (PType s _) -> Just (s, True)
    Just _ -> Nothing
    Nothing -> (\t -> (varTypeSort t, False)) <$> sVars stk M.!? v

makeBound :: Ident -> LocalCtxM ()
makeBound v = modify (\loc -> loc {lBound = S.insert v (lBound loc)})

insertLocal :: Ident -> LocalCtxM ()
insertLocal v = modify (\loc -> loc {lNewVars = S.insert v (lNewVars loc)})

ensureLocal :: Ident -> LocalCtxM Ident
ensureLocal v = do
  ctx <- ask
  Locals bd nv <- get
  case lookupLocal ctx v of
    Just (PType s _) -> return s
    Just _ -> throwError "hypothesis used as variable"
    Nothing -> do
      s <- lift (fst <$> ask) >>= getVarM v
      put (Locals bd (S.insert v nv))
      return $ varTypeSort s
