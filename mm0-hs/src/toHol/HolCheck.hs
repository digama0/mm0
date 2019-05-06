module HolCheck where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Q
import qualified Data.Set as S
import Environment (Ident)
import HolTypes

-- A HDef is a definition of a term depending on some variables,
-- i.e. T As xs = t[xs, As].
-- The dummy list names bound variables for alpha renaming.
data HDef = HDef {
  hdRVars :: [(Ident, SType)],
  hdLVars :: [(Ident, Sort)],
  hdRet :: Sort,
  hdVal :: Term,
  hdDummy :: [Ident] } deriving (Show)

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

type ProofM = StateT (M.Map Ident GType) Maybe

checkDecls :: [HDecl] -> Maybe GlobalCtx
checkDecls ds = go ds (GlobalCtx S.empty M.empty M.empty M.empty) where
  go [] gctx = return gctx
  go (d : ds) gctx = addDecl gctx d >>= go ds

addDecl :: GlobalCtx -> HDecl -> Maybe GlobalCtx
addDecl gctx = addDecl' where

  addDecl' :: HDecl -> Maybe GlobalCtx
  addDecl' (HDSort s) = do
    guard (S.notMember s (gSorts gctx))
    return $ gctx {gSorts = S.insert s (gSorts gctx)}
  addDecl' (HDTerm x t) = do
    guard (M.notMember x (gTerms gctx))
    return $ gctx {gTerms = M.insert x t (gTerms gctx)}
  addDecl' (HDDef x ts ss e vs) = do
    guard (M.notMember x (gTerms gctx))
    let ctx = mkLC ts ss
    r <- inferTerm ctx e
    guard (allInTerm (S.fromList ((fst <$> ss) ++ vs)) e)
    return $ gctx {
      gTerms = M.insert x (HType (snd <$> ts) (SType (snd <$> ss) r)) (gTerms gctx),
      gDefs = M.insert x (HDef ts ss r e vs) (gDefs gctx) }
  addDecl' (HDThm x t@(TType ts hs (GType ss r)) pr) = do
    guard (M.notMember x (gThms gctx))
    mapM_ (\(vs, p) -> do
      guard (length vs == length hs)
      let ctx = mkLC ts ss
      evalStateT (inferProof ctx p) (M.fromList (zip vs hs)) >>= guard . (r ==)
     ) pr
    return $ gctx {gThms = M.insert x t (gThms gctx)}

  inferTerm :: LocalCtx -> Term -> Maybe Sort
  inferTerm ctx (LVar v) = lcLVar ctx v
  inferTerm ctx (RVar v vs) = do
    SType ss r <- lcRVar ctx v
    mapM (lcLVar ctx) vs >>= guard . (ss ==)
    return r
  inferTerm ctx (HApp t es vs) = do
    HType ts (SType ss r) <- gTerms gctx M.!? t
    mapM (inferSLam ctx) es >>= guard . (ts ==)
    mapM (lcLVar ctx) vs >>= guard . (ss ==)
    return r
  inferTerm ctx HTSorry = fail "sorry found"

  inferSLam :: LocalCtx -> SLam -> Maybe SType
  inferSLam ctx (SLam ss t) = SType (snd <$> ss) <$> go ctx ss where
    go :: LocalCtx -> [(Ident, Sort)] -> Maybe Sort
    go ctx [] = inferTerm ctx t
    go ctx ((x, s) : ss) = go (lcInsert x s ctx) ss

  inferProofLam :: LocalCtx -> HProofLam -> ProofM GType
  inferProofLam ctx (HProofLam ss p) = GType ss <$> go ctx ss where
    go :: LocalCtx -> [(Ident, Sort)] -> ProofM Term
    go ctx [] = inferProof ctx p
    go ctx ((x, s) : ss) = go (lcInsert x s ctx) ss

  inferProof :: LocalCtx -> HProof -> ProofM Term
  inferProof ctx (HHyp n ys) = get >>= \heap -> lift $ do
    GType ts r <- heap M.!? n
    mapM (\x -> (,) x <$> lcLVar ctx x) ys >>= guard . (ts ==)
    return r
  inferProof ctx (HThm t es ps ys) = do
    TType ts hs (GType ss r) <- lift $ gThms gctx M.!? t
    lift $ mapM (inferSLam ctx) es >>= guard . (snd <$> ts ==)
    let m = M.fromList (zip (fst <$> ts) es)
    mapM (inferProofLam ctx) ps >>= guard . (substGType m <$> hs ==)
    lift $ mapM (\x -> (,) x <$> lcRVar ctx x) ys >>= guard . (ts ==)
    lift $ mapM (lcLVar ctx) ys >>= guard . (snd <$> ss ==)
    return $ vsubstTerm (M.fromList (zip (fst <$> ss) ys)) r
  inferProof ctx (HSave n (HProofLam ss p) ys) = do
    lift $ mapM (\x -> (,) x <$> lcLVar ctx x) ys >>= guard . (ss ==)
    r <- inferProof ctx p
    modify (M.insert n (GType ss r))
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
  inferConv ctx (CCong t ps xs) = do
    (es, es', ts') <- unzip3 <$> mapM (inferConvLam ctx) ps
    HType ts (SType ss r) <- lift $ gTerms gctx M.!? t
    guard (ts == ts')
    lift $ mapM (lcLVar ctx) xs >>= guard . (ss ==)
    return (HApp t es xs, HApp t es' xs, r)
  inferConv ctx (CDef t es xs ys) = do
    HDef ts ss r e vs <- lift $ gDefs gctx M.!? t
    lift $ mapM (inferSLam ctx) es >>= guard . (snd <$> ts ==)
    lift $ mapM (\x -> (,) x <$> lcLVar ctx x) xs >>= guard . (ss ==)
    guard (length ys == length vs)
    let e' = alphaTerm (M.fromList (zip ys vs)) $
             vsubstTerm (M.fromList (zip (fst <$> ss) xs)) $
             substTerm (M.fromList (zip (fst <$> ts) es)) e
    return (HApp t es xs, e', r)
