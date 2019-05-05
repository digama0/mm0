module HolCheck where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Q
import qualified Data.Set as S
import Environment (Ident)

type Sort = Ident
-- An SType is a type of the form s1 -> ... sn -> t where
-- si and t are basic types (sorts). Regular MM0 variables have an SType
data SType = SType [Sort] Sort deriving (Eq)

-- An HType is a type of the form s1 -> ... sn -> t where
-- si and t are simple types. MM0 term constructors have this type.
-- Full HOL is not needed.
data HType = HType [SType] SType

data SLam = SLam [(Ident, Sort)] Term deriving (Eq)

data Term =
    LVar Ident
  | RVar Ident [Ident]
  | HApp Ident [SLam] [Ident]
  deriving (Eq)

-- A GType is the type of a MM0 statement. It corresponds to the HOL statement
-- !xs. |- t, where t is a wff term depending on xs.
data GType = GType [(Ident, Sort)] Term deriving (Eq)

-- A TType is the type of a MM0 theorem. The STypes are the regular variables,
-- and the GTypes are the hypotheses. It corresponds to the HOL statement
-- !As. G1 -> ... -> Gn -> G' where the A's are higher order (SType) variables
-- and the G's are GTypes.
data TType = TType [(Ident, SType)] [GType] GType

-- A HDef is a definition of a term depending on some variables,
-- i.e. T As xs = t[xs, As].
-- The dummy list names bound variables for alpha renaming.
data HDef = HDef {
  hdRVars :: [(Ident, SType)],
  hdLVars :: [(Ident, Sort)],
  hdRet :: Sort,
  hdVal :: Term,
  hdDummy :: [Ident] }

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

-- A proof of !xs. |- ph. Variable lambdas are only allowed in certain
-- positions in HProof, so we make that explicit.
data HProofLam = HProofLam [(Ident, Sort)] HProof

data HProof =
    HHyp Ident [Ident]
  -- ^ |- [ys/xs] ph, if (!xs. |- ph) is hypothesis i
  -- in the proof context. In MM0 xs and ys will always be the same
  | HThm Ident [SLam] [HProofLam] [Ident]
  -- ^ If T : !As. G1 -> ... -> Gn -> !xs. |- ph, given expressions Ss and
  -- subproofs of [Ss/As] Gi, and variables ys, produce a proof of
  -- [ys/xs] [Ss/As] ph. In some HOL systems this requires an additional beta rule
  | HSave Ident HProofLam [Ident]
  -- ^ Abstract and save this proof in the local dictionary.
  -- Similar to dict[n] <- !xs. |- ph ; return |- [ys/xs] ph.
  -- In MM0 xs and ys are the same. The saved value is accessible via HHyp
  | HForget HProofLam
  -- ^ Given a proof of !xs. |- ph, where ph does not depend on xs,
  -- produce a proof of |- ph.
  -- Requires that the sort not be free (i.e. is inhabited)
  | HConv HConv HProof
  -- ^ Proof by conversion (definitional equality).
  -- From |- ph = ph' and |- ph infer |- ph'.
  -- Some HOL systems use a built in equality, for others this is automatic

data HConvLam = HConvLam [(Ident, Sort)] HConv

data HConv =
    CRefl Term
  -- ^ |- e = e
  | CSymm HConv
  -- ^ |- e1 = e2 => |- e2 = e1
  | CTrans HConv HConv
  -- ^ |- e1 = e2 => |- e2 = e3 => |- e1 = e3
  | CCong Ident [HConvLam] [Ident]
  -- ^ |- ei = ei' => |- T es xs = T es' xs
  | CDef Ident [SLam] [Ident] [Ident]
  -- ^ |- T es xs = D es xs ys, where ys names the bound vars
  -- in the definition D of T

type ProofM = StateT (M.Map Ident GType) Maybe

data HDecl =
    HDSort Sort
  -- ^ Introduce a new sort
  | HDTerm Ident HType
  -- ^ Define a new term constructor T
  | HDDef Ident [(Ident, SType)] [(Ident, Sort)] Term [Ident]
  -- ^ Define !As. !xs. T As xs = t{ys}, where ys gives the names of
  -- bound variables in t
  | HDThm Ident TType (Maybe ([Ident], HProof))
  -- ^ Prove a theorem or assert an axiom Th : !As. |- Gs => !xs. |- ph.
  -- The proof, if given, derives |- ph in the context with As, xs, Gs.

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

  substGType :: M.Map Ident SLam -> GType -> GType
  substGType m (GType ss r) = GType ss (substTerm m r)

  substSLam :: M.Map Ident SLam -> SLam -> SLam
  substSLam m (SLam vs t) = SLam vs (substTerm m t)

  substTerm :: M.Map Ident SLam -> Term -> Term
  substTerm m v@(LVar _) = v
  substTerm m (RVar v ys) = case m M.! v of
    SLam ss t -> vsubstTerm (M.fromList (zip (fst <$> ss) ys)) t
  substTerm m (HApp t es vs) = HApp t (substSLam m <$> es) vs

  vsubst :: M.Map Ident Ident -> Ident -> Ident
  vsubst m v = M.findWithDefault v v m

  vsubstSLam :: M.Map Ident Ident -> SLam -> SLam
  vsubstSLam m (SLam vs t) = SLam vs $
    vsubstTerm (foldr M.delete m (fst <$> vs)) t

  vsubstTerm :: M.Map Ident Ident -> Term -> Term
  vsubstTerm m (LVar x) = LVar (vsubst m x)
  vsubstTerm m v@(RVar _ _) = v
  vsubstTerm m (HApp t es vs) = HApp t (vsubstSLam m <$> es) (vsubst m <$> vs)

  nfTerm :: S.Set Ident -> Term -> Bool
  nfTerm s (LVar x) = S.notMember x s
  nfTerm s (RVar _ xs) = all (`S.notMember` s) xs
  nfTerm s (HApp t es vs) = all (nfSLam s) es && all (`S.notMember` s) vs

  nfSLam :: S.Set Ident -> SLam -> Bool
  nfSLam s (SLam vs t) = nfTerm (foldr S.delete s (fst <$> vs)) t

  alphaSLam :: M.Map Ident Ident -> SLam -> SLam
  alphaSLam m (SLam vs t) =
    SLam ((\(x, s) -> (vsubst m x, s)) <$> vs) (alphaTerm m t)

  alphaTerm :: M.Map Ident Ident -> Term -> Term
  alphaTerm m (LVar x) = LVar (vsubst m x)
  alphaTerm m (RVar v vs) = RVar v (vsubst m <$> vs)
  alphaTerm m (HApp t es vs) = HApp t (alphaSLam m <$> es) (vsubst m <$> vs)

  allInTerm :: S.Set Ident -> Term -> Bool
  allInTerm s (LVar x) = S.member x s
  allInTerm s (RVar _ xs) = all (`S.member` s) xs
  allInTerm s (HApp t es vs) = all (allInSLam s) es && all (`S.member` s) vs

  allInSLam :: S.Set Ident -> SLam -> Bool
  allInSLam s (SLam vs t) = all (`S.member` s) (fst <$> vs) && allInTerm s t
