{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module MM0.HOL.ToHol where

import Control.Monad.RWS.Strict hiding (local, asks)
import Control.Monad.Trans.Reader
import Data.Maybe
import Data.Foldable
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import MM0.HOL.Types
import MM0.Kernel.Environment
import MM0.Kernel.Types
import MM0.Util

data HTermData = HTermData {
  htArgs :: [PBinder],   -- ^ Arguments
  htRet :: DepType,      -- ^ Return value sort
  htDef :: Maybe ([(VarName, Sort)], SExpr) } -- ^ Definition

data HThmData = HThmData {
  haVars :: [PBinder],      -- ^ Sorts of the variables (bound and regular)
  haHyps :: [GType],        -- ^ Hypotheses
  haRet :: GType,           -- ^ Conclusion (translated)
  haVRet :: SExpr }         -- ^ Conclusion

data ToHolState = ToHolState {
  thPos :: Int,
  thSorts :: M.Map Sort Bool,
  thTerms :: M.Map TermName HTermData,
  thThms :: M.Map ThmName HThmData }

type ToHolM = RWST () (Endo [WithComment HDecl]) ToHolState (Either String)

toHol :: [WCStmt] -> Either String [WithComment HDecl]
toHol = \pfs -> do
  (_, _, Endo f) <- runRWST (mapM_ trStmt pfs) () $
    ToHolState 0 M.empty M.empty M.empty
  return (f [])
  where
  trStmt :: WCStmt -> ToHolM ()
  trStmt (WC c (StmtSort x sd)) = do
    tell (Endo (WC c (HDSort x) :))
    modify $ \g -> g {
      thSorts = M.insert x (sFree sd) (thSorts g) }
  trStmt (WC c (StmtTerm x args ty)) = do
    tell (Endo (WC c (HDTerm x (translateTerm args ty)) :))
    modify $ \g -> g {
      thTerms = M.insert x (HTermData args ty Nothing) (thTerms g) }
  trStmt (WC c (StmtAxiom x args hs ret)) = do
    g <- get
    let td@(TType _ hs' ret') = translateAxiom g args hs ret
    tell (Endo (WC c (HDThm x td Nothing) :))
    put $ g {thThms = M.insert x (HThmData args hs' ret' ret) (thThms g)}
  trStmt (WC c (StmtDef x vs ret ds def _)) = do
    g <- get
    let (rv, lv, e) = translateDef g vs ret ds def
    tell (Endo (WC c (HDDef x rv lv (dSort ret) e) :))
    modify $ \g' -> g' {
      thTerms = M.insert x (HTermData vs ret (Just (ds, def))) (thTerms g') }
  trStmt (WC c (StmtThm x args hs ret ds pf _)) = do
    g <- get
    let (ty@(TType _ hs' ret'), p) = translateThm g args hs ret ds pf
    tell (Endo (WC c (HDThm x ty (Just p)) :))
    modify $ \g' -> g' {
      thThms = M.insert x (HThmData args hs' ret' ret) (thThms g') }
  trStmt (WC _ (StepInout _)) = return ()

getLocal :: M.Map Ident PBinder -> Ident -> Sort
getLocal m v = case m M.! v of
  PBound _ t -> t
  _ -> error "not a bound var"

trBinders :: [PBinder] -> ([(Ident, SType)], M.Map Ident PBinder)
trBinders = go M.empty where
  go m [] = ([], m)
  go m (p@(PBound v _) : bis) = go (M.insert v p m) bis
  go m (p@(PReg v (DepType t ts)) : bis) =
    let (rs', m') = go (M.insert v p m) bis in
    ((v, SType (getLocal m <$> ts) t) : rs', m')

translateTerm :: [PBinder] -> DepType -> HType
translateTerm args (DepType t ts) =
  let (rs', ctx) = trBinders args in
  HType (snd <$> rs') $ SType (getLocal ctx <$> ts) t

translateAxiom :: ToHolState -> [PBinder] -> [SExpr] -> SExpr -> TType
translateAxiom g args hs ret =
  let (rs', ctx) = trBinders args in
  TType rs' (trGExpr g ctx args <$> hs) (trGExpr g ctx args ret)

fvBind :: [PBinder] -> Term -> [(Ident, Sort)]
fvBind vs t = mapMaybe g vs where
  fvs = fvLTerm t
  g (PBound x s) | S.member x fvs = Just (x, s)
  g _ = Nothing

uclose :: [PBinder] -> Term -> GType
uclose vs t = GType (fvBind vs t) t

trGExpr :: ToHolState -> M.Map VarName PBinder -> [PBinder] -> SExpr -> GType
trGExpr g ctx bis = uclose bis . trExpr g ctx

trExpr :: ToHolState -> M.Map VarName PBinder -> SExpr -> Term
trExpr g ctx = trExpr' where
  trExpr' (SVar v) = case ctx M.! v of
    PBound _ _ -> LVar v
    PReg _ (DepType _ xs) -> RVar v xs
  trExpr' (App t es) =
    let HTermData bis ty _ = thTerms g M.! t in
    uncurry (HApp t) (trApp ty bis es)

  trApp :: DepType -> [PBinder] -> [SExpr] -> ([SLam], [Ident])
  trApp (DepType _ ts) = go M.empty where
    go :: M.Map Ident (Ident, Sort) -> [PBinder] -> [SExpr] -> ([SLam], [Ident])
    go m [] [] = ([], fst . (m M.!) <$> ts)
    go m (PBound x t : bis) (SVar e : es) = go (M.insert x (e, t) m) bis es
    go _ (PBound _ _ : _) (_ : _) = error "bad proof"
    go m (PReg _ (DepType _ ts') : bis) (e : es) =
      let (ls, xs) = go m bis es in
      (SLam ((m M.!) <$> ts') (trExpr' e) : ls, xs)
    go _ _ _ = error "incorrect number of arguments"

trPBinders :: [PBinder] -> ([(VarName, SType)], M.Map VarName PBinder)
trPBinders = go M.empty where
  go m [] = ([], m)
  go m (bi@(PBound v _) : bis) = go (M.insert v bi m) bis
  go m (bi@(PReg v (DepType t ts)) : bis) =
    mapFst ((v, SType (binderSort . (m M.!) <$> ts) t) :) $ go (M.insert v bi m) bis

translateDef :: ToHolState -> [PBinder] -> DepType -> [(VarName, Sort)] -> SExpr ->
  ([(VarName, SType)], [(VarName, Sort)], Term)
translateDef g vs (DepType _ ts) ds e =
  let (rs, ctx) = trPBinders vs
      ctx' = foldl' (\ctx2 (x, s) -> M.insert x (PBound x s) ctx2) ctx ds
  in (rs, (\v -> (v, binderSort (ctx M.! v))) <$> ts, trExpr g ctx' e)

translateThm :: ToHolState -> [PBinder] -> [(VarName, SExpr)] -> SExpr ->
  [(VarName, Sort)] -> Proof -> (TType, ([Ident], HProof))
translateThm g args hs ret ds pf =
  let (rs, ctx) = trPBinders args
      hs' = mapSnd (trGExpr g ctx args) <$> hs
      ret' = trGExpr g ctx args ret
      ty = TType rs (snd <$> hs') ret'
      ctx' = foldl' (\ctx2 (x, s) -> M.insert x (PBound x s) ctx2) ctx ds
      hs'' = (\(v, GType xs t) -> (v, (fvLTerm t, HHyp v (fst <$> xs), t))) <$> hs'
      initSt = ToHolProofState (varToSlot <$> ctx') ctx' (M.fromList hs'')
  in (ty, (fst <$> hs, snd3 $ runReader (trProof g pf) initSt))

data HExpr = HExpr (S.Set Ident) Term deriving (Show)
type HProofF = (S.Set Ident, HProof, Term)

data ToHolProofState = ToHolProofState {
  psCtx :: M.Map VarName HExpr,
  psLVars :: M.Map VarName PBinder,
  psHyps :: M.Map VarName HProofF }

type ToHolProofM = Reader ToHolProofState

varToSlot :: PBinder -> HExpr
varToSlot (PBound v _) = HExpr (S.singleton v) (LVar v)
varToSlot (PReg v (DepType _ vs)) = HExpr (S.fromList vs) (RVar v vs)

substSExpr :: ToHolState -> M.Map VarName Term -> SExpr -> Term
substSExpr g subst = substSExpr' where
  substSExpr' (SVar v) = subst M.! v
  substSExpr' (App t es) =
    let HTermData bis ty _ = thTerms g M.! t in
    uncurry (HApp t) (substApp ty bis es)

  substApp :: DepType -> [PBinder] -> [SExpr] -> ([SLam], [Ident])
  substApp (DepType _ ts) = go M.empty where
    go :: M.Map VarName (Ident, Sort) -> [PBinder] -> [SExpr] -> ([SLam], [Ident])
    go m [] [] = ([], fst . (m M.!) <$> ts)
    go m (PBound x t : bis) (SVar v : es) =
      let LVar z = subst M.! v in go (M.insert x (z, t) m) bis es
    go _ (PBound _ _ : _) (_ : _) = error "bad proof"
    go m (PReg _ (DepType _ ts') : bis) (e : es) =
      mapFst (SLam ((m M.!) <$> ts') (substSExpr' e) :) (go m bis es)
    go _ _ _ = error "incorrect number of arguments"

reflTerm :: HConv -> Maybe Term
reflTerm (CRefl e) = Just e
reflTerm _ = Nothing

reflLam :: HConvLam -> Maybe SLam
reflLam (HConvLam vs c) = SLam vs <$> reflTerm c

type TrThm = (S.Set Ident, M.Map Ident SLam, M.Map Ident Term, [SLam], [HProofLam], [Ident])
type TrConv = (S.Set Ident, SExpr, SExpr, HConv, Term, Term)

trProof :: ToHolState -> Proof -> ToHolProofM HProofF
trProof g = trProof' where
  trProof' :: Proof -> ToHolProofM HProofF
  trProof' (PHyp h) = asks ((M.! h) . psHyps)
  trProof' (PThm t es ps) = do
    let HThmData bis hs ret ret' = thThms g M.! t
    (fv, _, subst, ls, ps', xs) <- trThm hs ret bis es ps
    trForget (fv, HThm t ls ps' xs, substSExpr g subst ret')
  trProof' (PConv _ c p) = do
    (fv, _, _, c', _, t) <- trConv True c
    (_, p', _) <- trProof' p
    trForget (fv, HConv c' p', t)
  trProof' (PLet h p1 p2) = do
    pf <- trProof' p1
    local (\st -> st {psHyps = M.insert h pf (psHyps st)}) $ trProof' p2
  trProof' PSorry = return (S.empty, HSorry, HTSorry)

  trForget :: HProofF -> ToHolProofM HProofF
  trForget (fv, p, ty) = do
    let fv' = fvLTerm ty
    if S.size fv == S.size fv' then
      return (fv', p, ty)
    else do
      let ds = S.toList (S.difference fv fv')
      m <- asks psLVars
      return (fv', HForget ty
        (HProofLam ((\d -> (d, binderSort (m M.! d))) <$> ds) p), ty)

  trPTExpr :: SExpr -> ToHolProofM (S.Set Ident, Term)
  trPTExpr e = do
    lvs <- asks psLVars
    let t = trExpr g lvs e
    return (fvLTerm t, t)

  trThm :: [GType] -> GType -> [PBinder] -> [SExpr] -> [Proof] -> ToHolProofM TrThm
  trThm hs (GType rv _) = trThmArgs M.empty S.empty M.empty M.empty id where
    trThmArgs :: M.Map Ident (Ident, Sort) -> S.Set Ident -> M.Map Ident SLam ->
      M.Map Ident Term -> ([SLam] -> [SLam]) -> [PBinder] -> [SExpr] -> [Proof] -> ToHolProofM TrThm
    trThmArgs m s ls q f [] [] ps = trThmHyps (f []) m s ls q hs ps
    trThmArgs m s ls q f (PBound x t : bis) (SVar v : es) ps =
      trThmArgs (M.insert x (v, t) m) s ls (M.insert x (LVar v) q) f bis es ps
    trThmArgs _ _ _ _ _ (PBound _ _ : _) (_ : _) _ = error "bad proof"
    trThmArgs m s ls q f (PReg v (DepType _ ts) : bis) (e : es) ps = do
      (fv, e') <- trPTExpr e
      let xts = (m M.!) <$> ts
      let l = SLam xts e'
      trThmArgs m (s <> foldr S.delete fv (fst <$> xts))
        (M.insert v l ls) (M.insert v e' q) (f . (l :)) bis es ps
    trThmArgs _ _ _ _ _ _ _ _ = error "incorrect number of arguments"

    trThmHyps :: [SLam] -> M.Map Ident (Ident, Sort) -> S.Set Ident -> M.Map Ident SLam ->
      M.Map Ident Term -> [GType] -> [Proof] -> ToHolProofM TrThm
    trThmHyps ls m s es q = go id where
      go :: ([HProofLam] -> [HProofLam]) -> [GType] -> [Proof] -> ToHolProofM TrThm
      go f [] [] = let xs = fst . (m M.!) . fst <$> rv in
        return (s <> S.fromList xs, es, q, ls, f [], xs)
      go f (GType hv _ : hs') (p : ps) =
        trProof' p >>= \(_, p', _) ->
          go (f . (HProofLam ((m M.!) . fst <$> hv) p' :)) hs' ps
      go _ _ _ = error "incorrect number of arguments"

  trConv :: Bool -> Conv -> ToHolProofM TrConv
  trConv _ (CVar v) = do
    HExpr s t <- asks ((M.! v) . psCtx)
    return (s, SVar v, SVar v, CRefl t, t, t)
  trConv sym (CSym c) = trConv (not sym) c
  trConv sym (CApp t cs) = do
    let HTermData bis ty _ = thTerms g M.! t
    (s, es1, es2, cls, ts1, ts2, xs) <- trConvApp sym ty bis cs
    return (s <> S.fromList xs, App t es1, App t es2,
      CCong t cls xs, HApp t ts1 xs, HApp t ts2 xs)
  trConv sym (CUnfold t es _ c) = do
    let e' = App t es
    lvs <- asks psLVars
    let t'@(HApp _ ts xs) = trExpr g lvs e'
    (s1, _, e2, c2, _, t2) <- trConv False c
    let s' = fvLTerm t' <> s1
    let c' = CTrans (CDef t ts xs) c2
    return $ if sym then (s', e2, e', CSymm c', t2, t') else (s', e', e2, c', t', t2)

  trConvApp :: Bool -> DepType -> [PBinder] -> [Conv] ->
    ToHolProofM (S.Set Ident, [SExpr], [SExpr], [HConvLam], [SLam], [SLam], [Ident])
  trConvApp sym (DepType _ ts) = go M.empty where
    go m [] [] = return (mempty, [], [], [], [], [], fst . (m M.!) <$> ts)
    go m (PBound x t : bis) (c : cs) = f c where
      f (CSym c') = f c'
      f (CVar e) = do
        (s1, es1, es2, cls, ts1, ts2, xs) <- go (M.insert x (e, t) m) bis cs
        return (s1, SVar e : es1, SVar e : es2, cls, ts1, ts2, xs)
      f _ = error "bad proof"
    go m (PReg _ (DepType _ ts') : bis) (c : cs) = do
      (s1, e1, e2, c', t1, t2) <- trConv sym c
      (s2, es1, es2, cls, ts1, ts2, xs) <- go m bis cs
      let vs = (m M.!) <$> ts'
      return (foldr S.delete s1 (fst <$> vs) <> s2, e1 : es1, e2 : es2,
        HConvLam vs c' : cls, SLam vs t1 : ts1, SLam vs t2 : ts2, xs)
    go _ _ _ = error "incorrect number of arguments"
