module MM0.FromMM.Closure (closure) where

import Control.Monad.State
import Control.Monad (when)
import Data.Bifunctor
import qualified Data.Set as S
import qualified Data.Text as T
import MM0.Kernel.Environment (SExpr(..))
import MM0.FromMM.Types

closure :: MMDatabase -> [Label] -> (S.Set Sort, S.Set Label)
closure db = \ls -> execState (mapM_ checkStmt ls) (S.empty, S.empty) where

  addSort :: Label -> State (S.Set Sort, S.Set Label) ()
  addSort x = modify $ first (S.insert x)

  addStmt :: Label -> State (S.Set Sort, S.Set Label) ()
  addStmt x = modify $ second (S.insert x)

  checkStmt :: Label -> State (S.Set Sort, S.Set Label) ()
  checkStmt x = do
    (_, sl) <- get
    when (S.notMember x sl) $ do
      addStmt x
      case getStmtM db x of
        Just (_, Term _ (hs, _) (_, e) _) -> do
          mapM_ checkHyp hs
          checkExpr e
        Just (_, Thm _ (hs, _) (_, e) pr) -> do
          mapM_ checkHyp hs
          checkExpr e
          mapM_ (\(ds, p) -> mapM_ (checkStmt . fst) ds >> checkProof p) pr
        Just (_, Hyp (VHyp s _)) -> addSort s
        Just (_, Hyp (EHyp _ e)) -> checkExpr e
        Just (_, Alias th) -> checkStmt th
        Nothing -> error $ "statement " ++ T.unpack x ++ " not found in the MM file"

  checkHyp :: (VarStatus, Label) -> State (S.Set Sort, S.Set Label) ()
  checkHyp (_, x) = checkStmt x >> case snd $ getStmt db x of
    Hyp (VHyp s _) -> addSort s
    Hyp (EHyp _ e) -> checkExpr e
    _ -> error "bad hyp"

  checkExpr :: MMExpr -> State (S.Set Sort, S.Set Label) ()
  checkExpr (SVar _) = return ()
  checkExpr (App t es) = checkStmt t >> mapM_ checkExpr es

  checkProof :: MMProof -> State (S.Set Sort, S.Set Label) ()
  checkProof (PSave p) = checkProof p
  checkProof (PTerm t ps) = checkStmt t >> mapM_ checkProof ps
  checkProof (PThm t ps) = checkStmt t >> mapM_ checkProof ps
  checkProof _ = return ()
