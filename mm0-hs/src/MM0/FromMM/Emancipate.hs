module MM0.FromMM.Emancipate (emancipate) where

import Control.Monad.State
import Data.Maybe
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import MM0.Kernel.Environment (SExpr(..))
import MM0.FromMM.Types

emancipate :: MMDatabase -> MMDatabase
emancipate db = execState (mapM_ emancipateDecl (mDecls db)) db

emancipateDecl :: Decl -> State MMDatabase ()
emancipateDecl (Stmt x) = get >>= \db -> case snd $ getStmt db x of
  Term (hs, _) _ Nothing ->
    let s = collectBound hs in
    updateDecl x hs $ if all ((== VSBound) . fst) hs then S.empty else s
  Term (hs, _) (_, e) (Just _) ->
    updateDecl x hs $ execState (checkExpr db False e) S.empty
  Thm (hs, _) (_, e) pr ->
    updateDecl x hs $ flip execState S.empty $ do
      mapM_ (checkHyp db) hs
      checkExpr db False e
      mapM_ (checkProof db . snd) pr
  _ -> return ()
emancipateDecl _ = return ()

collectBound :: [(VarStatus, Label)] -> S.Set Label
collectBound = go S.empty where
  go s [] = s
  go s ((VSBound, v) : vs) = go (S.insert v s) vs
  go s (_ : vs) = go s vs

checkHyp :: MMDatabase -> (VarStatus, Label) -> State (S.Set Label) ()
checkHyp db (VSHyp, x) = case snd $ getStmt db x of
  Hyp (EHyp _ e) -> checkExpr db True e
  _ -> return ()
checkHyp _ (_, _) = return ()

checkExpr :: MMDatabase -> Bool -> MMExpr -> State (S.Set Label) ()
checkExpr db hy = modify . checkExpr' where
  checkExpr' :: MMExpr -> S.Set Label -> S.Set Label
  checkExpr' (SVar v) = if hy then S.insert v else id
  checkExpr' (App t es) = checkApp hs es where
    Term (hs, _) _ _ = snd $ getStmt db t

  checkApp :: [(VarStatus, Label)] -> [MMExpr] -> S.Set Label -> S.Set Label
  checkApp [] [] = id
  checkApp ((VSBound, _) : hs) (SVar v : es) = checkApp hs es . S.insert v
  checkApp (_ : hs) (e : es) = checkApp hs es . checkExpr' e
  checkApp _ _ = error "bad proof"

checkProof :: MMDatabase -> MMProof -> State (S.Set Label) ()
checkProof db = modify . checkProof' where
  checkProof' :: MMProof -> S.Set Label -> S.Set Label
  checkProof' (PTerm t ps) = checkApp hs ps where
    Term (hs, _) _ _ = snd $ getStmt db t
  checkProof' (PThm t ps) = checkApp hs ps where
    Thm (hs, _) _ _ = snd $ getStmt db t
  checkProof' (PSave p) = checkProof' p
  checkProof' _ = id

  checkApp :: [(VarStatus, Label)] -> [MMProof] -> S.Set Label -> S.Set Label
  checkApp [] [] = id
  checkApp ((VSBound, _) : hs) (PHyp _ v _ : ps) = checkApp hs ps . S.insert v
  checkApp (_ : hs) (p : ps) = checkApp hs ps . checkProof' p
  checkApp _ _ = error "bad proof"

updateDecl :: Label -> [(VarStatus, Label)] -> S.Set Label -> State MMDatabase ()
updateDecl x hs s = case updateHyps s hs of
  Nothing -> return ()
  Just hs' -> modify $ \db -> db {mStmts = M.adjust (go hs') x $ mStmts db}
  where
  go hs' (n, Term (_, dv) e p) = (n, Term (hs', dv) e p)
  go hs' (n, Thm (_, dv) e p) = (n, Thm (hs', dv) e p)
  go _ _ = error "bad decl"

updateHyps :: S.Set Label -> [(VarStatus, Label)] -> Maybe [(VarStatus, Label)]
updateHyps s = go where
  go [] = Nothing
  go ((VSBound, v) : vs) | S.notMember v s =
    Just $ (VSFree, v) : fromMaybe vs (go vs)
  go (v : vs) = (v :) <$> go vs
