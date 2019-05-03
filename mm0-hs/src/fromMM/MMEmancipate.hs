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
emancipateDecl (Stmt x) = get >>= \db -> case mStmts db M.! x of
  Term (hs, _) _ e Nothing ->
    let s = collectBound hs in
    updateDecl x hs $ if all fst hs then S.empty else s
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

collectBound :: [(Bool, Label)] -> S.Set Label
collectBound = go S.empty where
  go s [] = s
  go s ((b, v) : vs) = go (if b then S.insert v s else s) vs

checkHyp :: MMDatabase -> (Bool, Label) -> State (S.Set Label) ()
checkHyp _ (True, _) = return ()
checkHyp db (_, x) = case mStmts db M.! x of
  Hyp (EHyp _ e) -> checkExpr db e
  _ -> return ()

checkExpr :: MMDatabase -> MMExpr -> State (S.Set Label) ()
checkExpr db = modify . checkExpr' where
  checkExpr' :: MMExpr -> S.Set Label -> S.Set Label
  checkExpr' (SVar v) = id
  checkExpr' (App t es) = checkApp hs es where
    Term (hs, _) _ _ _ = mStmts db M.! t

  checkApp :: [(Bool, Label)] -> [MMExpr] -> S.Set Label -> S.Set Label
  checkApp [] [] = id
  checkApp ((True, _) : hs) (SVar v : es) = checkApp hs es . S.insert v
  checkApp (_ : hs) (e : es) = checkApp hs es . checkExpr' e

checkProof :: MMDatabase -> Proof -> State (S.Set Label) ()
checkProof db = modify . checkProof' where
  checkProof' :: Proof -> S.Set Label -> S.Set Label
  checkProof' (PTerm t ps) = checkApp hs ps where
    Term (hs, _) _ _ _ = mStmts db M.! t
  checkProof' (PThm t ps) = checkApp hs ps where
    Thm (hs, _) _ _ _ = mStmts db M.! t
  checkProof' (PSave p) = checkProof' p
  checkProof' _ = id

  checkApp :: [(Bool, Label)] -> [Proof] -> S.Set Label -> S.Set Label
  checkApp [] [] = id
  checkApp ((True, _) : hs) (PHyp v _ : ps) = checkApp hs ps . S.insert v
  checkApp (_ : hs) (p : ps) = checkApp hs ps . checkProof' p



updateDecl :: Label -> [(Bool, Label)] -> S.Set Label -> State MMDatabase ()
updateDecl x hs s = case updateHyps s hs of
  Nothing -> return ()
  Just hs' -> modify $ \db -> db {mStmts = M.adjust (\case
    Term (_, dv) s e p -> Term (hs', dv) s e p
    Thm (_, dv) s e p -> Thm (hs', dv) s e p) x $ mStmts db}

updateHyps :: S.Set Label -> [(Bool, Label)] -> Maybe [(Bool, Label)]
updateHyps s = go where
  go [] = Nothing
  go ((True, v) : vs) | S.notMember v s =
    Just $ (False, v) : fromMaybe vs (go vs)
  go (v : vs) = (v :) <$> go vs
