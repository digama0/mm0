module HolCheck where

import Control.Monad.Except
import Control.Monad.Trans.State
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
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

withContext :: MonadError String m => T.Text -> m a -> m a
withContext s m = catchError m (\e -> throwError ("while checking " ++ T.unpack s ++ ":\n" ++ e))

checkDecls :: [HDecl] -> Either String GlobalCtx
checkDecls ds = go ds (GlobalCtx S.empty M.empty M.empty M.empty) where
  go [] gctx = return gctx
  go (d : ds') gctx = addDecl gctx d >>= go ds'

addDecl :: GlobalCtx -> HDecl -> Either String GlobalCtx
addDecl gctx = addDecl' where

  addDecl' :: HDecl -> Either String GlobalCtx
  addDecl' (HDSort s) = do
    guard (S.notMember s (gSorts gctx))
    return $ gctx {gSorts = S.insert s (gSorts gctx)}
  addDecl' (HDTerm x t) = do
    guard (M.notMember x (gTerms gctx))
    return $ gctx {gTerms = M.insert x t (gTerms gctx)}
  addDecl' (HDDef x ts ss r e) = do
    guard (M.notMember x (gTerms gctx))
    let ctx = mkLC ts ss
    withContext x $ inferTerm ctx e >>= guard . (r ==)
    return $ gctx {
      gTerms = M.insert x (HType (snd <$> ts) (SType (snd <$> ss) r)) (gTerms gctx),
      gDefs = M.insert x (HDef ts ss r e) (gDefs gctx) }
  addDecl' (HDThm x t@(TType ts hs (GType ss r)) pr) = do
    guard (M.notMember x (gThms gctx))
    withContext x $ forM_ pr $ \(vs, p) -> do
      guard (length vs == length hs)
      let ctx = mkLC ts ss
      r' <- evalStateT (inferProof ctx p) (M.fromList (zip vs hs))
      guardError ("result does not match theorem statement:\n    " ++
        show r ++ "\n != " ++ show r') (alphaTerm M.empty r r')
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
      fromJustError ("term '" ++ T.unpack t ++ "' not found") $ gTerms gctx M.!? t
    ts' <- mapM (inferSLam ctx) es
    fromJustError (show ctx ++ " |/- " ++ show (HApp t es vs) ++
      ", where:\n  " ++ T.unpack t ++ " : " ++ show ty ++
      foldMap (\(e, t') -> "\n  " ++ show e ++ " : " ++ show t') (zip es ts')) $ do
      guard (ts == ts')
      mapM (lcLVar ctx) vs >>= guard . (ss ==)
      return r
  inferTerm _ HTSorry = fail "sorry found"

  inferSLam :: LocalCtx -> SLam -> Either String SType
  inferSLam ctx (SLam ss t) = SType (snd <$> ss) <$> go ctx ss where
    go :: LocalCtx -> [(Ident, Sort)] -> Either String Sort
    go ctx' [] = inferTerm ctx' t
    go ctx' ((x, s) : ss') = go (lcInsert x s ctx') ss'

  inferProofLam :: LocalCtx -> HProofLam -> ProofM GType
  inferProofLam ctx (HProofLam ss p) = GType ss <$> go ctx ss where
    go :: LocalCtx -> [(Ident, Sort)] -> ProofM Term
    go ctx' [] = inferProof ctx' p
    go ctx' ((x, s) : ss') = go (lcInsert x s ctx') ss'

  inferProof :: LocalCtx -> HProof -> ProofM Term
  inferProof ctx p@(HHyp n ys) = get >>= \heap -> lift $ do
    ty@(GType ts r) <- fromJustError ("hyp " ++ T.unpack n ++ " not found") $ heap M.!? n
    fromJustError ("failed to check " ++
      show p ++ "\n  where ctx[" ++ T.unpack n ++ "]: " ++ show ty) $ do
      mapM (\x -> (,) x <$> lcLVar ctx x) ys >>= guard . (ts ==)
      return r
  inferProof ctx p@(HThm t es ps ys) = do
    ty@(TType ts hs (GType ss r)) <-
      fromJustError ("theorem '" ++ T.unpack t ++ "' not found") $ gThms gctx M.!? t
    ts' <- lift $ mapM (inferSLam ctx) es
    let m = M.fromList (zip (fst <$> ts) es)
    hs' <- mapM (inferProofLam ctx) ps
    let err = "failed to check " ++ show p ++
          ", where:\n  " ++ T.unpack t ++ " : " ++ show ty ++
          foldMap (\(e, t') -> "\n  " ++ show e ++ " : " ++ show t') (zip es ts') ++
          foldMap (\(e, t') -> "\n  " ++ show e ++ " : " ++ show t') (zip ps hs')
    guardError (err ++ "\ntype mismatch in regular vars") $ (snd <$> ts) == ts'
    unless (all2 alphaGType (substGType m <$> hs) hs') $
      forM_ (zip hs hs') $ \(h, h') -> do
        guardError (err ++ "\nhypothesis substitution does not match:\n  " ++
          show h ++ "\n  substituted(" ++ show m ++ ")\n   = " ++ show (substGType m h) ++
          "\n  != " ++ show h') $ alphaGType (substGType m h) h'
    fromJustError err $ do
      mapM (lcLVar ctx) ys >>= guard . (snd <$> ss ==)
      let (ss', r') = substAbs m ss r
      return $ vsubstTerm (M.fromList (zip (fst <$> ss') ys)) r'
  inferProof ctx p'@(HSave n (HProofLam ss p) ys) = do
    r <- inferProof ctx p
    modify (M.insert n (GType ss r))
    fromJustError ("failed to check " ++ show p') $ do
      mapM (\x -> (,) x <$> lcLVar ctx x) ys >>= guard . (ss ==)
      return r
  inferProof ctx p'@(HForget t p) = do
    GType ss t' <- inferProofLam ctx p
    fromJustError ("failed to check " ++ show p' ++
      "\n  term " ++ show t ++
      "\n  contains variables in " ++ show (fst <$> ss)) $ do
      guard (nfTerm (S.fromList (fst <$> ss)) t)
      guard (alphaTerm M.empty t t')
      return t
  inferProof ctx (HConv eq p) = do
    (t1, t2, _) <- inferConv ctx eq
    inferProof ctx p >>= guard . (t1 ==)
    return t2
  inferProof _ HSorry = fail "sorry found"

  inferConvLam :: LocalCtx -> HConvLam -> ProofM (SLam, SLam, SType)
  inferConvLam ctx (HConvLam ss p) = do
    (e1, e2, t) <- go ctx ss
    return (SLam ss e1, SLam ss e2, SType (snd <$> ss) t)
    where
    go :: LocalCtx -> [(Ident, Sort)] -> ProofM (Term, Term, Sort)
    go ctx' [] = inferConv ctx' p
    go ctx' ((x, s) : ss') = go (lcInsert x s ctx') ss'

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
      fromJustError ("term '" ++ T.unpack t ++ "' not found") $ gTerms gctx M.!? t
    fromJustError ("failed to check " ++
      show c ++ "\n  where " ++ T.unpack t ++ ": " ++ show ty) $ do
      guard (ts == ts')
      mapM (lcLVar ctx) xs >>= guard . (ss ==)
      return (HApp t es xs, HApp t es' xs, r)
  inferConv ctx c@(CDef t es xs) = do
    HDef ts ss r e <- fromJustError ("def '" ++ T.unpack t ++ "' not found") $
      gDefs gctx M.!? t
    ts' <- lift $ mapM (inferSLam ctx) es
    fromJustError ("failed to check " ++ show c ++
      "\n  where " ++ show (HDDef t ts ss r e)) $ do
      guard ((snd <$> ts) == ts')
      mapM (\x -> (,) x <$> lcLVar ctx x) xs >>= guard . (ss ==)
      let (ss', l) = substAbs (M.fromList (zip (fst <$> ts) es)) ss e
          e' = vsubstTerm (M.fromList (zip (fst <$> ss') xs)) l
      return (HApp t es xs, e', r)
