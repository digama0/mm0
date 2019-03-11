module SpecCheck(checkAST) where

import Control.Monad.State.Class
import Control.Monad.RWS.Strict
import Control.Monad.Except
import Data.Maybe
import Data.List
import Debug.Trace
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Sequence as Q
import AST
import Environment
import ParserEnv
import LocalContext
import MathParser
import Util

data TCState = TCState {
  env :: Environment,
  eParser :: ParserEnv }

data Spec =
    SSort Ident SortData
  | SDecl Ident Decl
  | SThm {
      tName :: Ident,
      tArgs :: [PBinder],
      tHyps :: [SExpr],
      tReturn :: SExpr }
  deriving (Show)

type SpecM = RWST Stack (Q.Seq Spec) (Environment, ParserEnv) (Either String)

modifyParser :: (Environment -> ParserEnv -> Either String ParserEnv) -> SpecM ()
modifyParser f = do
  (e, p) <- get
  p' <- lift $ f e p
  put (e, p')

emit :: Spec -> SpecM ()
emit = tell . Q.singleton

insertSort :: Ident -> SortData -> SpecM ()
insertSort v sd = do
  (e, p) <- get
  s' <- lift $ insertNew ("sort " ++ v ++ " already declared") v sd (eSorts e)
  put (e {eSorts = s'}, p)
  tell (Q.singleton (SSort v sd))

insertDecl :: Ident -> Decl -> SpecM ()
insertDecl v d = do
  (e, p) <- get
  trace ("insertDecl " ++ v ++ ": " ++ show d) (return ())
  d' <- lift $ insertNew ("decl " ++ v ++ " already declared") v d (eDecls e)
  put (e {eDecls = d'}, p)
  emit (SDecl v d)

insertVars :: [Ident] -> VarType -> SpecM a -> SpecM a
insertVars vs ty = local (\s -> s {sVars = f vs (sVars s)}) where
  f :: [Ident] -> Vars -> Vars
  f [] = id
  f (v:vs) = f vs . M.insert v ty

getVar' :: MonadError String m => Ident -> Stack -> m VarType
getVar' v s = fromJustError "type depends on unknown variable" (sVars s M.!? v)

getVar :: Ident -> SpecM VarType
getVar v = do s <- ask; getVar' v s

pushStack :: Stack -> Stack
pushStack s = Stack (sVars s) (Just s)

evalSpecM :: SpecM a -> Either String (a, Q.Seq Spec)
evalSpecM m = evalRWST m (Stack M.empty Nothing) (Environment M.empty M.empty, newParserEnv)

checkAST :: AST -> Either String (Q.Seq Spec)
checkAST ast = snd <$> evalSpecM (checkDecls ast)

checkDecls :: [Stmt] -> SpecM ()
checkDecls [] = return ()
checkDecls (Sort v sd : ds) = insertSort v sd >> checkDecls ds
checkDecls (Var ids ty : ds) = insertVars ids ty (checkDecls ds)
checkDecls (Term x vs ty : ds) =
  checkTerm x vs ty DTerm >>= insertDecl x >> checkDecls ds
checkDecls (Axiom x vs ty : ds) =
  checkAssert x vs ty DAxiom >>= insertDecl x >> checkDecls ds
checkDecls (Theorem x vs ty : ds) = do
  env <- fst <$> get
  checkAssert x vs ty (SThm x) >>= emit
  checkDecls ds
checkDecls (Def x vs ty def : ds) =
  checkDef x vs ty def >>= insertDecl x >> checkDecls ds
checkDecls (Notation n : ds) = do
  (e, pe) <- get
  modifyParser (addNotation n)
  checkDecls ds
checkDecls (Output k v bi : ds) =
  throwError ("output-kind " ++ show k ++ " not supported")
checkDecls (Block ss : ds) = local pushStack (checkDecls ss) >> checkDecls ds

checkTerm :: Ident -> [Binder] -> DepType -> ([PBinder] -> DepType -> a) -> SpecM a
checkTerm x vs ty mk = do
  ((bis, dummies, hyps), loc) <- runLocalCtxM' $
    processBinders vs $ \vs' ds hs -> checkType ty >> return (vs', ds, hs)
  stk <- ask
  lift $ do
    guardError (x ++ ": terms are not permitted to use var declarations") (S.null (lNewVars loc))
    guardError (x ++ ": dummy variables not permitted in terms") (null dummies)
    guardError (x ++ ": hypotheses not permitted in terms") (null hyps)
    bis <- setBound stk loc bis
    return (mk bis ty)

checkAssert :: Ident -> [Binder] -> Formula -> ([PBinder] -> [SExpr] -> SExpr -> a) -> SpecM a
checkAssert x vs fmla mk = do
  ((bis, dummies, hyps, ret), loc) <- runLocalCtxM' $
    processBinders vs $ \vs' ds hs -> do
      sexp <- parseFormula fmla
      return (vs', ds, hs, sexp)
  stk <- ask
  lift $ do
    guardError (x ++ ": dummy variables not permitted in axiom/theorem") (null dummies)
    bis <- setBound stk loc bis
    return (mk bis hyps ret)

checkDef :: Ident -> [Binder] -> DepType -> Maybe Formula -> SpecM Decl
checkDef x vs ty Nothing = checkTerm x vs ty (\bs r -> DDef bs r Nothing)
checkDef x vs ty (Just defn) = do
  ((bis, dummies, hyps, defn'), Locals sbd nv) <- runLocalCtxM' $
    processBinders vs $ \vs' ds hs -> do
      checkType ty
      defn' <- parseFormula defn
      return (vs', ds, hs, defn')
  stk <- ask
  lift $ do
    guardError (x ++ ": hypotheses not permitted in terms") (null hyps)
    let dummies' = S.foldr' (\v -> M.insert v (varTypeSort $ sVars stk M.! v)) dummies nv
    bis <- setBound stk (Locals sbd S.empty) bis
    return (DDef bis ty $ Just (dummies, defn'))

runLocalCtxM' :: LocalCtxM a -> SpecM (a, Locals)
runLocalCtxM' m = RWST $ \stk e ->
  (\r -> (r, e, mempty)) <$> runLocalCtxM m stk e

processBinders :: [Binder] -> ([PBinder] -> M.Map Ident Ident -> [SExpr] -> LocalCtxM a) -> LocalCtxM a
processBinders = go M.empty where
  go m [] f = f [] m []
  go m (b:bs) f = processBinder b
    (\b' -> go m bs (f . (b':)))
    (\d t -> go (M.insert d t m) bs f)
    (\h -> go m bs (\bs' ds' hs -> case bs' of
      [] -> f [] ds' (h : hs)
      _ -> throwError "hypotheses must come after variable bindings"))

  processBinder :: Binder -> (PBinder -> LocalCtxM a) ->
    (Ident -> Ident -> LocalCtxM a) -> (SExpr -> LocalCtxM a) -> LocalCtxM a
  processBinder (Binder (LDummy v) (TType (DepType t ts))) _ g _ = do
    guardError "dummy variable has dependent type" (null ts)
    lcmLocal (lcDummyCons v t) (g v t)
  processBinder (Binder (LDummy _) (TFormula _)) _ _ _ =
    throwError "dummy hypothesis not permitted (use '_' instead)"
  processBinder (Binder v (TType ty)) f _ _ = do
    checkType ty
    let bi = PReg (fromMaybe "_" (localName v)) ty
    lcmLocal (lcRegCons bi) (f bi)
  processBinder (Binder _ (TFormula s)) _ _ h = parseFormula s >>= h

checkType :: DepType -> LocalCtxM ()
checkType (DepType v vs) = do
  Locals _ nv <- get
  mapM_ (\v' -> ensureLocal v' >> makeBound v') vs

setBound :: Stack -> Locals -> [PBinder] -> Either String [PBinder]
setBound stk (Locals sbd nv) bis = do
  let (nvBd, nvReg) = partition (`S.member` sbd) (S.toList nv)
  let bis2 = (\v -> PBound v $ varTypeSort $ sVars stk M.! v) <$> nvBd
  (bd, bis') <- collectBound (bis ++ bis2)
  return $ bis' ++ ((\v -> PReg v $ varTypeToDep bd $ sVars stk M.! v) <$> nvReg)
  where
  collectBound :: [PBinder] -> Either String ([Ident], [PBinder])
  collectBound [] = return ([], [])
  collectBound (PBound v t : bis) =
    (\(vs, bis') -> (v:vs, PBound v t : bis')) <$> collectBound bis
  collectBound (PReg v ty : bis) | S.member v sbd = case ty of
    DepType t [] -> (\(vs, bis') -> (v:vs, PBound v t : bis')) <$> collectBound bis
    _ -> throwError "bound variable has dependent type"
  collectBound (bi : bis) = (\(vs, bis') -> (vs, bi : bis')) <$> collectBound bis
