module MMEmancipate (emancipate) where

import Control.Monad.State hiding (liftIO)
import Data.Maybe
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Environment (SExpr(..))
import MMTypes

emancipate :: MMDatabase -> MMDatabase
emancipate db = execState (mapM_ emancipateDecl (mDecls db)) db

emancipateDecl :: Decl -> State MMDatabase ()
emancipateDecl (Stmt x) = get >>= \db -> case snd $ mStmts db M.! x of
  Term (hs, _) _ e Nothing ->
    let s = collectBound hs in
    updateDecl x hs $ if all ((== VSBound) . fst) hs then S.empty else s
  Term (hs, _) _ e (Just _) ->
    let s = collectBound hs in
    updateDecl x hs $ execState (checkExpr db e) S.empty
  Thm (hs, dv) _ e pr ->
    let s = collectBound hs in
    updateDecl x hs $ execState (do
      mapM_ (checkHyp db) hs
      checkExpr db e
      mapM_ (\(ds, p) -> checkProof db p) pr) S.empty
  _ -> return ()
emancipateDecl _ = return ()

collectBound :: [(VarStatus, Label)] -> S.Set Label
collectBound = go S.empty where
  go s [] = s
  go s ((VSBound, v) : vs) = go (S.insert v s) vs
  go s (_ : vs) = go s vs

checkHyp :: MMDatabase -> (VarStatus, Label) -> State (S.Set Label) ()
checkHyp db (VSHyp, x) = case snd $ mStmts db M.! x of
  Hyp (EHyp _ e) -> checkExpr db e
  _ -> return ()
checkHyp _ (_, _) = return ()

checkExpr :: MMDatabase -> MMExpr -> State (S.Set Label) ()
checkExpr db = modify . checkExpr' where
  checkExpr' :: MMExpr -> S.Set Label -> S.Set Label
  checkExpr' (SVar v) = id
  checkExpr' (App t es) = checkApp hs es where
    Term (hs, _) _ _ _ = snd $ mStmts db M.! t

  checkApp :: [(VarStatus, Label)] -> [MMExpr] -> S.Set Label -> S.Set Label
  checkApp [] [] = id
  checkApp ((VSBound, _) : hs) (SVar v : es) = checkApp hs es . S.insert v
  checkApp (_ : hs) (e : es) = checkApp hs es . checkExpr' e

checkProof :: MMDatabase -> Proof -> State (S.Set Label) ()
checkProof db = modify . checkProof' where
  checkProof' :: Proof -> S.Set Label -> S.Set Label
  checkProof' (PTerm t ps) = checkApp hs ps where
    Term (hs, _) _ _ _ = snd $ mStmts db M.! t
  checkProof' (PThm t ps) = checkApp hs ps where
    Thm (hs, _) _ _ _ = snd $ mStmts db M.! t
  checkProof' (PSave p) = checkProof' p
  checkProof' _ = id

  checkApp :: [(VarStatus, Label)] -> [Proof] -> S.Set Label -> S.Set Label
  checkApp [] [] = id
  checkApp ((VSBound, _) : hs) (PHyp v _ : ps) = checkApp hs ps . S.insert v
  checkApp (_ : hs) (p : ps) = checkApp hs ps . checkProof' p

updateDecl :: Label -> [(VarStatus, Label)] -> S.Set Label -> State MMDatabase ()
updateDecl x hs s = case updateHyps s hs of
  Nothing -> return ()
  Just hs' -> modify $ \db -> db {mStmts = M.adjust (\case
    (n, Term (_, dv) s e p) -> (n, Term (hs', dv) s e p)
    (n, Thm (_, dv) s e p) -> (n, Thm (hs', dv) s e p)) x $ mStmts db}

updateHyps :: S.Set Label -> [(VarStatus, Label)] -> Maybe [(VarStatus, Label)]
updateHyps s = go where
  go [] = Nothing
  go ((VSBound, v) : vs) | S.notMember v s =
    Just $ (VSFree, v) : fromMaybe vs (go vs)
  go (v : vs) = (v :) <$> go vs
