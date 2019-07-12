module FindBundled (findBundled, bundle, reportBundled, Bundles) where

import Control.Monad.RWS.Strict hiding (liftIO)
import qualified Data.Map.Strict as M
import qualified Data.IntMap as I
import qualified Data.Set as S
import MMTypes
import Util

type Bundles = M.Map [Int] Int

bundle :: (Ord a) => [a] -> [Int]
bundle = go M.empty 0 where
  go _ _ [] = []
  go m n (a:as) = case m M.!? a of
    Just i -> i : go m n as
    Nothing -> n : go (M.insert a n m) (n+1) as

type BundledReport = S.Set ((Label, Maybe [Int]), (Label, [Int]))
type FindBundledM = RWS () BundledReport (M.Map Label Bundles)

findBundled :: MMDatabase -> M.Map Label Bundles
findBundled db = fst $ execRWS (findBundled' db False) () M.empty

reportBundled :: MMDatabase -> M.Map Label Bundles -> BundledReport
reportBundled db m = snd $ execRWS (findBundled' db True) () m

findBundled' :: MMDatabase -> Bool -> FindBundledM ()
findBundled' db strict = mapM_ checkDecl (mDecls db) where
  pureArgs :: M.Map Label [Int]
  pureArgs = M.mapMaybe f (mStmts db) where
    f (_, Thm (hs, _) _ _) =
      case go hs 0 of { [] -> Nothing; l -> Just l } where
      go [] _ = []
      go ((p, _):ls) n | vsPure p = n : go ls (n+1)
      go (_:ls) n = go ls (n+1)
    f _ = Nothing

  checkDecl :: Decl -> FindBundledM ()
  checkDecl (Stmt s) = case snd $ getStmt db s of
    Thm fr _ (Just (_, p)) -> checkProof (s, Nothing) 0 (allDistinct fr) p
    _ -> return ()
  checkDecl _ = return ()

  allDistinct :: Frame -> I.IntMap Int
  allDistinct (hs, _) = go hs 0 0 I.empty where
    go [] _ _ m = m
    go ((p, _):ls) k i m | vsPure p = go ls (k+1) (i+1) (I.insert k i m)
    go (_:ls) k i m = go ls (k+1) i m

  checkProof :: (Label, Maybe [Int]) -> Int -> I.IntMap Int -> Proof -> FindBundledM ()
  checkProof x k im = go where
    go (PSave p) = go p
    go (PThm t ps) = do
      mapM_ go ps
      forM_ (pureArgs M.!? t) $ \l ->
        let l' = (\n -> case ps !! n of
              PHyp _ i -> Left (im I.! i)
              PDummy i -> Right i
              _ -> error "bad proof") <$> l
        in unless (allUnique l') $ do
          let b = bundle l'
          m <- gets (M.findWithDefault M.empty t)
          if not strict || M.member b m then do
              modify $ M.insert t (M.alter (Just . maybe k (min k)) b m)
              case getStmt db t of
                (_, Thm _ _ (Just (_, p))) ->
                  checkProof (t, Just b) (k+1) (I.fromList (zip l b)) p
                _ -> return ()
          else tell $ S.singleton (x, (t, b))
    go _ = return ()
