module SpecCheck() where

import Control.Monad.Trans.Reader
import Control.Monad.Trans.State (StateT)
import Control.Monad.State.Class
import Control.Monad.Except
import Data.Maybe
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import AST
import Environment
import Util
import MathParser

data TCState = TCState {
  env :: Environment,
  eParser :: ParserEnv }

data ProofObligation = ProofObligation {
  tEnv :: Environment,
  tBound :: [Ident],
  tArgs :: [DepType],
  tHyps :: [SExpr],
  tReturn :: SExpr }

type SpecM = ReaderT Stack (StateT (Environment, ParserEnv) (Either String))

modifyEnv :: (Environment -> Either String Environment) -> SpecM ()
modifyEnv f = do
  (e, p) <- get
  e' <- lift $ lift $ f e
  put (e', p)

modifyParser :: (Environment -> ParserEnv -> Either String ParserEnv) -> SpecM ()
modifyParser f = do
  (e, p) <- get
  p' <- lift $ lift $ f e p
  put (e, p')

modifyStack :: (Stack -> Stack) -> SpecM a -> SpecM a
modifyStack = local

insertSort :: Ident -> SortData -> SpecM ()
insertSort v sd = modifyEnv $ \e -> do
  s' <- insertNew ("sort " ++ v ++ " already declared") v sd (eSorts e)
  return (e {eSorts = s'})

insertDecl :: Ident -> Decl -> SpecM ()
insertDecl v d = modifyEnv $ \e -> do
  d' <- insertNew ("decl " ++ v ++ " already declared") v d (eDecls e)
  return (e {eDecls = d'})

insertVars :: [Ident] -> VarType -> SpecM a -> SpecM a
insertVars vs ty = modifyStack (\s -> s {sVars = f vs (sVars s)}) where
  f :: [Ident] -> Vars -> Vars
  f [] = id
  f (v:vs) = f vs . M.insert v ty

getVar' :: MonadError String m => Ident -> Stack -> m VarType
getVar' v s = fromJustError "type depends on unknown variable" (sVars s M.!? v)

getVar :: Ident -> SpecM VarType
getVar v = do s <- ask; getVar' v s

pushStack :: Stack -> Stack
pushStack s = Stack (sVars s) (Just s)

checkAST :: AST -> SpecM [ProofObligation]
checkAST [] = return []
checkAST (Sort v sd : ds) = insertSort v sd >> checkAST ds
checkAST (Var ids ty : ds) = insertVars ids ty (checkAST ds)
checkAST (Term t vs ty : ds) = undefined
checkAST (Axiom t vs ty : ds) = undefined
checkAST (Theorem t vs ty : ds) = undefined
checkAST (Def t vs ty def : ds) = undefined
checkAST (Notation n : ds) = do
  (e, pe) <- get
  modifyParser (addNotation n)
  checkAST ds
checkAST (Output k v bi : ds) =
  throwError ("output-kind " ++ show k ++ " not supported")
checkAST (Block ss : ds) =
  (++) <$> modifyStack pushStack (checkAST ss) <*> checkAST ds

data PType = PType Ident [Ident] | PFormula SExpr
data PBinder = PBinder Local PType

data Locals = Locals {
  lBound :: S.Set Ident,
  lNewVars :: [Ident] }

type LCtx = [PBinder]
type LocalSpecM a = ReaderT (Stack, (Environment, ParserEnv))
  (StateT Locals (Either String)) a

lookupLocal :: LCtx -> Ident -> Maybe PType
lookupLocal [] _ = Nothing
lookupLocal (PBinder l ty : ls) v =
  if localName l == Just v then Just ty else lookupLocal ls v

makeBound :: Ident -> LocalSpecM ()
makeBound v = modify (\loc -> loc {lBound = S.insert v (lBound loc)})

ensureLocal :: Ident -> LCtx -> LocalSpecM ()
ensureLocal v ctx = do
  Locals bd nv <- get
  unless (isJust (lookupLocal ctx v) || v `elem` nv) $ do
    stk <- fst <$> ask
    getVar' v stk
    put (Locals bd (v : nv))

processBinders :: [Binder] -> ([PBinder] -> LCtx -> LocalSpecM a) -> LCtx -> LocalSpecM a
processBinders [] f = f []
processBinders (b:bs) f =
  processBinder b (\b' -> processBinders bs (f . (b':)))

processBinder :: Binder -> (PBinder -> LCtx -> LocalSpecM a) -> LCtx -> LocalSpecM a
processBinder (Binder l ty) f ctx = do
  b <- PBinder l <$> processType ty ctx
  f b (b : ctx)

processType :: Type -> LCtx -> LocalSpecM PType
processType (TType v vs) ctx = do
  Locals _ nv <- get
  mapM_ (\v' -> ensureLocal v' ctx >> makeBound v') vs
  return (PType v vs)
processType (TFormula s) ctx = do
  (_, (e, pe)) <- ask
  fmla <- lift $ lift $ parseFormula pe s
  return (PFormula fmla)
