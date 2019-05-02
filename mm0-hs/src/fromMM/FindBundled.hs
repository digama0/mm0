module FindBundled (findBundled, Bundles) where

import Control.Monad.State hiding (liftIO)
import Data.Maybe
import qualified Data.Map.Strict as M
import qualified Data.IntMap as I
import qualified Data.Set as S
import Environment (SortData(..))
import MMTypes
import Util

type Bundles = S.Set [Int]

bundle :: (Ord a) => [a] -> [Int]
bundle = go M.empty 0 where
  go m _ [] = []
  go m n (a:as) = case m M.!? a of
    Just i -> i : go m n as
    Nothing -> n : go (M.insert a n m) (n+1) as

findBundled :: MMDatabase -> M.Map Label Bundles
findBundled db = execState (mapM_ checkDecl (mDecls db)) M.empty where
  pureArgs :: M.Map Label [Int]
  pureArgs = M.mapMaybe f (mStmts db) where
    f (Thm (hs, _) _ _ _) =
      case go hs 0 of { [] -> Nothing; l -> Just l } where
      go [] _ = []
      go ((b, _):ls) n = if b then n : go ls (n+1) else go ls (n+1)
    f _ = Nothing

  checkDecl :: Decl -> State (M.Map Label Bundles) ()
  checkDecl (Stmt s) = case mStmts db M.! s of
    Thm fr _ _ (Just (_, p)) -> checkProof (allDistinct fr) p
    _ -> return ()
  checkDecl _ = return ()

  allDistinct :: Frame -> I.IntMap Int
  allDistinct (hs, _) = go hs 0 0 I.empty where
    go [] _ _ m = m
    go ((True, _):ls) k i m = go ls (k+1) (i+1) (I.insert k i m)
    go ((False, _):ls) k i m = go ls (k+1) i m

  checkProof :: I.IntMap Int -> Proof -> State (M.Map Label Bundles) ()
  checkProof m = go where
    go (PSave p) = go p
    go (PThm t ps) = do
      mapM_ go ps
      mapM_ (\l ->
        let l' = (\n -> case ps !! n of
              PHyp _ i -> Left (m I.! i)
              PDummy i -> Right i) <$> l in
        unless (allUnique l') $ do
          let b = bundle l'
          modify $ M.alter (Just . S.insert b . fromMaybe S.empty) t
          case mStmts db M.! t of
            Thm fr _ _ (Just (_, p)) -> checkProof (I.fromList (zip l b)) p
            _ -> return ()
        ) (pureArgs M.!? t)
    go _ = return ()
