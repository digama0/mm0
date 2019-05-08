module HolCheck where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Q
import qualified Data.Set as S
import Environment (Ident)
import HolTypes
import Util

-- A HDef is a definition of a term depending on some variables,
-- i.e. T As xs = t[xs, As].
-- The dummy list names bound variables for alpha renaming.
data HDef = HDef {
  hdRVars :: [(Ident, SType)],
  hdLVars :: [(Ident, Sort)],
  hdRet :: Sort,
  hdVal :: Term } deriving (Show)

data GlobalCtx = GlobalCtx {
  gSorts :: S.Set Sort,
  gTerms :: M.Map Ident HType,
  gThms :: M.Map Ident TType,
  gDefs :: M.Map Ident HDef }

type LocalCtx = (M.Map Ident Sort, M.Map Ident SType)

mkLC :: [(Ident, SType)] -> [(Ident, Sort)] -> LocalCtx
mkLC rc lc = (M.fromList lc, M.fromList rc)

lcInsert :: Ident -> Sort -> LocalCtx -> LocalCtx
lcInsert v s (lctx, rctx) = (M.insert v s lctx, rctx)

lcLVar :: LocalCtx -> Ident -> Maybe Sort
lcLVar (lctx, _) v = lctx M.!? v

lcRVar :: LocalCtx -> Ident -> Maybe SType
lcRVar (_, rctx) v = rctx M.!? v

type ProofM = StateT (M.Map Ident GType) (Either String)

checkDecls :: [HDecl] -> Either String GlobalCtx
checkDecls ds = go ds (GlobalCtx S.empty M.empty M.empty M.empty) where
  go [] gctx = return gctx
  go (d : ds) gctx = addDecl gctx d >>= go ds

addDecl :: GlobalCtx -> HDecl -> Either String GlobalCtx
addDecl gctx = addDecl' where

  addDecl' :: HDecl -> Either String GlobalCtx
  addDecl' (HDSort s) = do
    guard (S.notMember s (gSorts gctx))
    return $ gctx {gSorts = S.insert s (gSorts gctx)}
  addDecl' (HDTerm x t) = do
    guard (M.notMember x (gTerms gctx))
    return $ gctx {gTerms = M.insert x t (gTerms gctx)}
  addDecl' (HDDef x ts ss e) = do
    guard (M.notMember x (gTerms gctx))
    let ctx = mkLC ts ss
    r <- inferTerm ctx e
    return $ gctx {
      gTerms = M.insert x (HType (snd <$> ts) (SType (snd <$> ss) r)) (gTerms gctx),
      gDefs = M.insert x (HDef ts ss r e) (gDefs gctx) }
  addDecl' (HDThm x t@(TType ts hs (GType ss r)) pr) = do
    guard (M.notMember x (gThms gctx))
    forM_ pr $ \(vs, p) -> do
      guard (length vs == length hs)
      let ctx = mkLC ts ss
      evalStateT (inferProof ctx p) (M.fromList (zip vs hs)) >>= guard . (r ==)
    return $ gctx {gThms = M.insert x t (gThms gctx)}

  inferTerm :: LocalCtx -> Term -> Either String Sort
  inferTerm ctx (LVar v) =
    fromJustError (show ctx ++ " |- " ++ show (LVar v) ++ ": ?") $ lcLVar ctx v
  inferTerm ctx (RVar v vs) =
    fromJustError (show ctx ++ " |- " ++ show (RVar v vs) ++ ": ?") $ do
      SType ss r <- lcRVar ctx v
      mapM (lcLVar ctx) vs >>= guard . (ss ==)
      return r
  inferTerm ctx (HApp t es vs) = do
    ty@(HType ts (SType ss r)) <-
      fromJustError ("term '" ++ t ++ "' not found") $ gTerms gctx M.!? t
    ts' <- mapM (inferSLam ctx) es
    fromJustError (show ctx ++ " |/- " ++ show (HApp t es vs) ++
      ", where:\n  " ++ t ++ " : " ++ show ty ++
      foldMap (\(e, t) -> "\n  " ++ show e ++ " : " ++ show t) (zip es ts')) $ do
      guard (ts == ts')
      mapM (lcLVar ctx) vs >>= guard . (ss ==)
      return r
  inferTerm ctx HTSorry = fail "sorry found"

  inferSLam :: LocalCtx -> SLam -> Either String SType
  inferSLam ctx (SLam ss t) = SType (snd <$> ss) <$> go ctx ss where
    go :: LocalCtx -> [(Ident, Sort)] -> Either String Sort
    go ctx [] = inferTerm ctx t
    go ctx ((x, s) : ss) = go (lcInsert x s ctx) ss

  inferProofLam :: LocalCtx -> HProofLam -> ProofM GType
  inferProofLam ctx (HProofLam ss p) = GType ss <$> go ctx ss where
    go :: LocalCtx -> [(Ident, Sort)] -> ProofM Term
    go ctx [] = inferProof ctx p
    go ctx ((x, s) : ss) = go (lcInsert x s ctx) ss

  inferProof :: LocalCtx -> HProof -> ProofM Term
  inferProof ctx p@(HHyp n ys) = get >>= \heap -> lift $ do
    ty@(GType ts r) <- fromJustError ("hyp " ++ n ++ " not found") $ heap M.!? n
    fromJustError ("failed to check " ++
      show p ++ "\n  where ctx[" ++ n ++ "]: " ++ show ty) $ do
      mapM (\x -> (,) x <$> lcLVar ctx x) ys >>= guard . (ts ==)
      return r
  inferProof ctx p@(HThm t es ps ys) = do
    ty@(TType ts hs (GType ss r)) <-
      fromJustError ("theorem '" ++ t ++ "' not found") $ gThms gctx M.!? t
    ts' <- lift $ mapM (inferSLam ctx) es
    let m = M.fromList (zip (fst <$> ts) es)
    hs' <- mapM (inferProofLam ctx) ps
    fromJustError ("failed to check " ++ show p ++
      ", where:\n  " ++ t ++ " : " ++ show ty ++
      foldMap (\(e, t) -> "\n  " ++ show e ++ " : " ++ show t) (zip es ts') ++
      foldMap (\(e, t) -> "\n  " ++ show e ++ " : " ++ show t) (zip ps hs')) $ do
      guard $ (snd <$> ts) == ts'
      guard $ all2 alphaGType (substGType m <$> hs) hs'
      mapM (lcLVar ctx) ys >>= guard . (snd <$> ss ==)
      return $ vsubstTerm (M.fromList (zip (fst <$> ss) ys)) $ substTerm m r
  inferProof ctx p'@(HSave n (HProofLam ss p) ys) = do
    r <- inferProof ctx p
    modify (M.insert n (GType ss r))
    fromJustError ("failed to check " ++ show p') $ do
      mapM (\x -> (,) x <$> lcLVar ctx x) ys >>= guard . (ss ==)
      return r
  inferProof ctx (HForget p) = do
    GType ss t <- inferProofLam ctx p
    guard $ nfTerm (S.fromList (fst <$> ss)) t
    return t
  inferProof ctx (HConv eq p) = do
    (t1, t2, _) <- inferConv ctx eq
    inferProof ctx p >>= guard . (t1 ==)
    return t2
  inferProof ctx HSorry = fail "sorry found"

  inferConvLam :: LocalCtx -> HConvLam -> ProofM (SLam, SLam, SType)
  inferConvLam ctx (HConvLam ss p) = do
    (e1, e2, t) <- go ctx ss
    return (SLam ss e1, SLam ss e2, SType (snd <$> ss) t)
    where
    go :: LocalCtx -> [(Ident, Sort)] -> ProofM (Term, Term, Sort)
    go ctx [] = inferConv ctx p
    go ctx ((x, s) : ss) = go (lcInsert x s ctx) ss

  inferConv :: LocalCtx -> HConv -> ProofM (Term, Term, Sort)
  inferConv ctx (CRefl e) = do
    t <- lift $ inferTerm ctx e
    return (e, e, t)
  inferConv ctx (CSymm p) = do
    (e1, e2, r) <- inferConv ctx p
    return (e2, e1, r)
  inferConv ctx (CTrans p1 p2) = do
    (e1, e2, r) <- inferConv ctx p1
    (e2', e3, _) <- inferConv ctx p2
    guard (e2 == e2')
    return (e1, e3, r)
  inferConv ctx c@(CCong t ps xs) = do
    (es, es', ts') <- unzip3 <$> mapM (inferConvLam ctx) ps
    ty@(HType ts (SType ss r)) <-
      fromJustError ("term '" ++ t ++ "' not found") $ gTerms gctx M.!? t
    fromJustError ("failed to check " ++
      show c ++ "\n  where " ++ t ++ ": " ++ show ty) $ do
      guard (ts == ts')
      mapM (lcLVar ctx) xs >>= guard . (ss ==)
      return (HApp t es xs, HApp t es' xs, r)
  inferConv ctx c@(CDef t es xs) = do
    HDef ts ss r e <- fromJustError ("def '" ++ t ++ "' not found") $
      gDefs gctx M.!? t
    ts' <- lift $ mapM (inferSLam ctx) es
    fromJustError ("failed to check " ++ show c ++
      "\n  where " ++ show (HDDef t ts ss e)) $ do
      guard ((snd <$> ts) == ts')
      mapM (\x -> (,) x <$> lcLVar ctx x) xs >>= guard . (ss ==)
      let e' = vsubstTerm (M.fromList (zip (fst <$> ss) xs)) $
               substTerm (M.fromList (zip (fst <$> ts) es)) e
      return (HApp t es xs, e', r)
