module MM0.Kernel.SpecCheck (checkSpec, insertSpec) where

import Control.Monad.Except
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import qualified Data.Sequence as Q
import MM0.FrontEnd.AST
import MM0.Kernel.Environment
import MM0.Util

insertSpec' :: Spec -> Environment -> Either String Environment
insertSpec' (SSort v sd) e = do
  s' <- insertNew ("sort " ++ T.unpack v ++ " already declared") v sd (eSorts e)
  return (e {eSorts = s', eSpec = eSpec e Q.|> SSort v sd})
insertSpec' (SDecl v d) e = do
  -- trace ("insertDecl " ++ v ++ ": " ++ show d) (return ())
  d' <- insertNew ("decl " ++ T.unpack v ++ " already declared") v d (eDecls e)
  return (e {eDecls = d', eSpec = eSpec e Q.|> SDecl v d})
insertSpec' s e = return (e {eSpec = eSpec e Q.|> s})

insertSpec :: Spec -> Environment -> Either String Environment
insertSpec s e = checkSpec e s >> insertSpec' s e

withContext :: MonadError String m => T.Text -> m a -> m a
withContext s m = catchError m (\e -> throwError ("when adding " ++ T.unpack s ++ ": " ++ e))

checkSpec :: Environment -> Spec -> Either String ()
checkSpec _ (SSort _ _) = return ()
checkSpec e (SDecl x (DTerm bis ret)) = withContext x $ checkDef e bis ret Nothing
checkSpec e (SDecl x (DAxiom bis hs ret)) = withContext x $ do
  ctx <- checkBinders e bis
  mapM_ (provableSExpr e ctx) hs
  provableSExpr e ctx ret
checkSpec e (SDecl x (DDef bis ret defn)) = withContext x $ checkDef e bis ret defn
checkSpec e (SThm x bis hs ret) = withContext x $ do
  ctx <- checkBinders e bis
  mapM_ (provableSExpr e ctx) hs
  provableSExpr e ctx ret
checkSpec e (SInout (IOKString _ val)) =
  withContext "input/output" (checkSExpr e M.empty val (DepType "string" []))

checkDef :: Environment -> [PBinder] -> DepType ->
  Maybe (M.Map Ident Ident, SExpr) -> Either String ()
checkDef env bis ret defn = do
  ctx <- checkBinders env bis
  checkType ctx ret
  sd <- fromJustError "sort not found" (eSorts env M.!? dSort ret)
  guardError ("cannot declare term for pure sort '" ++ T.unpack (dSort ret) ++ "'") (not (sPure sd))
  case defn of
    Nothing -> return ()
    Just (dummy, e) -> do
      ctx2 <- traverse (\t -> do
        sd' <- fromJustError "sort not found" (eSorts env M.!? t)
        guardError ("cannot bind variable; sort '" ++ T.unpack t ++ "' is strict") (not (sStrict sd'))
        return (True, DepType t [])) dummy
      checkSExpr env (ctx <> ctx2) e ret

checkBinders :: Environment -> [PBinder] -> Either String (M.Map Ident (Bool, DepType))
checkBinders e = go M.empty where
  go :: M.Map Ident (Bool, DepType) -> [PBinder] -> Either String (M.Map Ident (Bool, DepType))
  go ctx (PBound x t : bis) = do
    sd <- fromJustError "sort not found" (eSorts e M.!? t)
    guardError ("cannot bind variable; sort '" ++ T.unpack t ++ "' is strict") (not (sStrict sd))
    go (M.insert x (True, DepType t []) ctx) bis
  go ctx (PReg x ty : bis) = do
    _ <- fromJustError "sort not found" (eSorts e M.!? dSort ty)
    checkType ctx ty >> go (M.insert x (False, ty) ctx) bis
  go ctx [] = return ctx

checkType :: M.Map Ident (Bool, DepType) -> DepType -> Either String ()
checkType ctx (DepType _ ts) = mapM_ ok ts where
  ok v = do
    (bd, _) <- fromJustError "variable not found" (ctx M.!? v)
    guardError "variable depends on regular variable" bd

provableSExpr :: Environment -> M.Map Ident (Bool, DepType) -> SExpr -> Either String ()
provableSExpr env ctx e = do
  t <- inferSExpr env ctx e
  sd <- fromJustError "sort not found" (eSorts env M.!? t)
  guardError "expression must be a provable sort" (sProvable sd)

checkSExpr :: Environment -> M.Map Ident (Bool, DepType) -> SExpr -> DepType -> Either String ()
checkSExpr env ctx e ty = do
  t <- inferSExpr env ctx e
  guardError ("type error, expected " ++ show (dSort ty) ++
    ", got " ++ show e ++ ": " ++ show t) (t == dSort ty)

inferSExpr :: Environment -> M.Map Ident (Bool, DepType) -> SExpr -> Either String Ident
inferSExpr _ ctx (SVar v) = do
  (_, DepType t _) <- fromJustError "variable not found" (ctx M.!? v)
  return t
inferSExpr env ctx (App f es) = do
  (ts, DepType t _) <- fromJustError "term not found" (getTerm env f)
  matchTypes env ctx es ts
  return t

matchTypes :: Environment -> M.Map Ident (Bool, DepType) -> [SExpr] -> [PBinder] -> Either String ()
matchTypes _ _ [] [] = return ()
matchTypes env ctx (e : es) (PBound _ t : bis) = do
  case e of
    SVar v -> fromJustError "variable not found" (ctx M.!? v) >>= \case
      (True, DepType t' _) -> guardError "type error" (t == t')
      _ -> throwError "non-bound variable in BV slot"
    _ -> throwError "non-bound variable in BV slot"
  matchTypes env ctx es bis
matchTypes env ctx (e : es) (PReg _ ty : bis) = do
  checkSExpr env ctx e ty
  matchTypes env ctx es bis
matchTypes _ _ _ _ = throwError "incorrect number of arguments"
