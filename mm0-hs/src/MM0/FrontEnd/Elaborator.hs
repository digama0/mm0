module MM0.FrontEnd.Elaborator (elabAST) where

import Control.Monad.Trans.State
import Control.Monad.Except
import Data.Maybe
import Data.Default
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import MM0.FrontEnd.AST
import MM0.Kernel.Environment
import MM0.FrontEnd.ParserEnv
import MM0.FrontEnd.LocalContext
import MM0.FrontEnd.MathParser
import qualified MM0.Kernel.SpecCheck as SpecCheck
import MM0.Util

type SpecM = StateT (Environment, ParserEnv) (Either String)

modifyEnv :: (Environment -> Either String Environment) -> SpecM ()
modifyEnv f = do
  (e, p) <- get
  e' <- lift $ f e
  put (e', p)

modifyParser :: (Environment -> ParserEnv -> Either String ParserEnv) -> SpecM ()
modifyParser f = do
  (e, p) <- get
  p' <- lift $ f e p
  put (e, p')

insertSpec :: Spec -> SpecM ()
insertSpec = modifyEnv . SpecCheck.insertSpec

insertSort :: Ident -> SortData -> SpecM ()
insertSort v sd = insertSpec (SSort v sd) >> modifyParser recalcCoeProv

insertDecl :: Ident -> Decl -> SpecM ()
insertDecl v d = insertSpec (SDecl v d)

evalSpecM :: SpecM a -> Either String (a, Environment)
evalSpecM m = do
  (a, (e, _)) <- runStateT m def
  return (a, e)

elabAST :: AST -> Either String Environment
elabAST ast = snd <$> evalSpecM (elabDecls ast)

elabDecls :: [Stmt] -> SpecM ()
elabDecls [] = return ()
elabDecls (Sort _ v sd : ds) = insertSort v sd >> elabDecls ds
elabDecls (Term _ x vs ty : ds) =
  elabTerm x vs ty DTerm >>= insertDecl x >> elabDecls ds
elabDecls (Axiom _ x vs ty : ds) =
  elabAssert x vs ty DAxiom >>= insertDecl x >> elabDecls ds
elabDecls (Theorem _ x vs ty : ds) = do
  elabAssert x vs ty (SThm x) >>= insertSpec
  elabDecls ds
elabDecls (Def _ x vs ty defn : ds) =
  elabDef x vs ty defn >>= insertDecl x >> elabDecls ds
elabDecls (Notation n : ds) = modifyParser (addNotation n) >> elabDecls ds
elabDecls (Inout (Input k s) : ds) = elabInout False k s >> elabDecls ds
elabDecls (Inout (Output k s) : ds) = elabInout True k s >> elabDecls ds

elabTerm :: Ident -> [Binder] -> DepType -> ([PBinder] -> DepType -> a) -> SpecM a
elabTerm x vs ty mk = do
  (bis, dummies, hyps) <- runLocalCtxM' $
    processBinders vs $ \vs' ds hs -> checkType ty >> return (vs', ds, hs)
  lift $ do
    guardError (T.unpack x ++ ": dummy variables not permitted in terms") (null dummies)
    guardError (T.unpack x ++ ": hypotheses not permitted in terms") (null hyps)
    return (mk bis ty)

elabAssert :: Ident -> [Binder] -> Formula -> ([PBinder] -> [SExpr] -> SExpr -> a) -> SpecM a
elabAssert x vs fmla mk = do
  (bis, dummies, hyps, ret) <- withContext x $ runLocalCtxM' $
    processBinders vs $ \vs' ds hs -> do
      sexp <- parseFormulaProv fmla
      return (vs', ds, hs, sexp)
  lift $ do
    guardError (T.unpack x ++ ": dummy variables not permitted in axiom/theorem") (null dummies)
    return (mk bis hyps ret)

elabDef :: Ident -> [Binder] -> DepType -> Maybe Formula -> SpecM Decl
elabDef x vs ty Nothing = elabTerm x vs ty (\bs r -> DDef bs r Nothing)
elabDef x vs ty (Just defn) = do
  (bis, dummies, hyps, defn') <- withContext x $ runLocalCtxM' $
    processBinders vs $ \vs' ds hs -> do
      checkType ty
      defn' <- parseFormula (dSort ty) defn
      return (vs', ds, hs, defn')
  lift $ do
    guardError (T.unpack x ++ ": hypotheses not permitted in terms") (null hyps)
    return (DDef bis ty $ Just (M.toList dummies, defn'))

elabInout :: Bool -> T.Text -> [Either Ident Formula] -> SpecM ()
elabInout out "string" [x] = do
  e <- runLocalCtxM' $ parseTermFmla "string" x
  insertSpec (SInout (IOKString out e))
elabInout _ "string" _ = throwError ("input/output-kind string takes one argument")
elabInout False k _ = throwError ("input-kind " ++ show k ++ " not supported")
elabInout True k _ = throwError ("output-kind " ++ show k ++ " not supported")

parseTermFmla :: Ident -> Either Ident Formula -> LocalCtxM SExpr
parseTermFmla _ (Left x) = do
  env <- readEnv
  case getTerm env x of
    Just ([], _) -> return (App x [])
    _ -> throwError ("input argument " ++ T.unpack x ++ " is not a nullary term constructor")
parseTermFmla s (Right f) = parseFormula s f

runLocalCtxM' :: LocalCtxM a -> SpecM a
runLocalCtxM' m = StateT $ \e -> (\r -> (r, e)) <$> runLocalCtxM m e

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
  processBinder (Binder (LBound v) (TType (DepType t ts))) f _ _ = do
    guardError "bound variable has dependent type" (null ts)
    let bi = PBound v t
    lcmLocal (lcRegCons bi) (f bi)
  processBinder (Binder (LDummy v) (TType (DepType t ts))) _ g _ = do
    guardError "dummy variable has dependent type" (null ts)
    lcmLocal (lcDummyCons v t) (g v t)
  processBinder (Binder (LDummy _) (TFormula _)) _ _ _ =
    throwError "dummy hypothesis not permitted (use '_' instead)"
  processBinder (Binder v (TType ty)) f _ _ = do
    checkType ty
    let bi = PReg (fromMaybe "_" (localName v)) ty
    lcmLocal (lcRegCons bi) (f bi)
  processBinder (Binder _ (TFormula s)) _ _ h = parseFormulaProv s >>= h

checkType :: DepType -> LocalCtxM ()
checkType (DepType _ vs) = mapM_ ensureBound vs
