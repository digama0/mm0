module MMClosure (closure) where

import Control.Monad.State hiding (liftIO)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Environment (SExpr(..))
import MMTypes

closure :: MMDatabase -> [Label] -> (S.Set Sort, S.Set Label)
closure db = \ls -> execState (mapM_ checkStmt ls) (S.empty, S.empty) where

  addSort :: Label -> State (S.Set Sort, S.Set Label) ()
  addSort x = modify $ \(ss, sl) -> (S.insert x ss, sl)

  addStmt :: Label -> State (S.Set Sort, S.Set Label) ()
  addStmt x = modify $ \(ss, sl) -> (ss, S.insert x sl)

  checkStmt :: Label -> State (S.Set Sort, S.Set Label) ()
  checkStmt x = do
    (_, sl) <- get
    when (S.notMember x sl) $ do
      addStmt x
      case mStmts db M.!? x of
        Just (_, Term (hs, _) _ e _) -> do
          mapM_ checkHyp hs
          checkExpr e
        Just (_, Thm (hs, _) _ e pr) -> do
          mapM_ checkHyp hs
          checkExpr e
          mapM_ (\(ds, p) -> checkProof p) pr
        Just (_, Hyp (VHyp s _)) -> addSort s
        Just (_, Hyp (EHyp _ e)) -> checkExpr e
        Nothing -> error $ "statement " ++ x ++ " not found in the MM file"

  checkHyp :: (Bool, Label) -> State (S.Set Sort, S.Set Label) ()
  checkHyp (_, x) = checkStmt x >> case snd $ mStmts db M.! x of
    Hyp (VHyp s _) -> addSort s
    Hyp (EHyp _ e) -> checkExpr e

  checkExpr :: MMExpr -> State (S.Set Sort, S.Set Label) ()
  checkExpr (SVar v) = return ()
  checkExpr (App t es) = checkStmt t >> mapM_ checkExpr es

  checkProof :: Proof -> State (S.Set Sort, S.Set Label) ()
  checkProof (PSave p) = checkProof p
  checkProof (PTerm t ps) = checkStmt t >> mapM_ checkProof ps
  checkProof (PThm t ps) = checkStmt t >> mapM_ checkProof ps
  checkProof _ = return ()
