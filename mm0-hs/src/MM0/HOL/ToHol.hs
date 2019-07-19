{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module MM0.HOL.ToHol where

import Control.Monad.Except
import Control.Monad.RWS.Strict
import Data.Maybe
import Data.Foldable
import qualified Control.Monad.Trans.State as ST
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Q
import qualified Data.IntMap as I
import qualified Data.Set as S
import qualified Data.Text as T
import MM0.HOL.Types
import MM0.Kernel.Environment
import MM0.Kernel.Types
import MM0.Util

data HTermData = HTermData {
  htName :: Ident,       -- ^ Name
  htArgs :: [PBinder],   -- ^ Arguments
  htRet :: DepType }     -- ^ Return value sort

data HDefData = HDefData {
  hdDummies :: [(Ident, Sort)],  -- ^ Dummy variables
  hdVal :: VExpr }               -- ^ Definition expr

data HThmData = HThmData {
  haName :: Ident,          -- ^ Name
  haVars :: [PBinder],      -- ^ Sorts of the variables (bound and regular)
  haHyps :: [GType],        -- ^ Hypotheses
  haRet :: GType,           -- ^ Conclusion (translated)
  haVRet :: SExpr }         -- ^ Conclusion

data ToHolState = ToHolState {
  thPos :: Int,
  thSorts :: Q.Seq (Sort, Bool),
  thSortIx :: M.Map Ident SortID,
  thTerms :: Q.Seq HTermData,
  thTermIx :: M.Map Ident TermID,
  thThms :: Q.Seq HThmData,
  thDefs :: I.IntMap HDefData }

thSort :: ToHolState -> SortID -> Sort
thSort g (SortID n) = fst (Q.index (thSorts g) n)

thTerm :: ToHolState -> TermID -> HTermData
thTerm g (TermID n) = Q.index (thTerms g) n

thThm :: ToHolState -> ThmID -> HThmData
thThm g (ThmID n) = Q.index (thThms g) n

varName :: VarID -> Ident
varName = T.pack . show

type ToHolM = RWST () (Endo [HDecl]) ToHolState (Either String)

toHol :: Environment -> Proofs -> Either String [HDecl]
toHol env = \pfs -> do
  (_, _, Endo f) <- runRWST (mapM_ trCmd pfs) () $
    ToHolState 0 Q.empty M.empty Q.empty M.empty Q.empty I.empty
  return (f [])
  where

  step :: ToHolM Spec
  step = do
    n <- state (\g -> (thPos g, g {thPos = thPos g + 1}))
    fromJustError "nothing more to prove" (eSpec env Q.!? n)

  trCmd :: ProofCmd -> ToHolM ()
  trCmd (StepSort x) = step >>= \case
    SSort x' sd | x == x' -> do
      tell (Endo (HDSort x :))
      modify $ \g -> g {
        thSorts = thSorts g Q.|> (x, sFree sd) }
    e -> throwError ("incorrect step 'sort " ++ T.unpack x ++ "', found " ++ show e)
  trCmd (StepTerm x) = step >>= \case
    SDecl x' (DTerm args ty) | x == x' -> do
      tell (Endo (HDTerm x (translateTerm args ty) :))
      modify $ \g -> g {
        thTerms = thTerms g Q.|> HTermData x args ty,
        thTermIx = M.insert x (TermID (Q.length (thTerms g))) (thTermIx g) }
    e -> throwError ("incorrect step 'term " ++ T.unpack x ++ "', found " ++ show e)
  trCmd (StepAxiom x) = step >>= \case
    SDecl x' (DAxiom args hs ret) | x == x' -> do
      g <- get
      let td@(TType _ hs' ret') = translateAxiom g args hs ret
      tell (Endo (HDThm x td Nothing :))
      put $ g {thThms = thThms g Q.|> HThmData x args hs' ret' ret}
    e -> throwError ("incorrect step 'axiom " ++ T.unpack x ++ "', found " ++ show e)
  trCmd (ProofDef x vs ret ds def st) = do
    when st $ step >> return ()
    g <- get
    let n = TermID (Q.length (thTerms g))
    let name = fromMaybe (T.pack $ show n) x
    let (bis, ty, rv, lv, r, e, ds') = translateDef g vs ret ds def
    tell (Endo (HDDef name rv lv r e :))
    modify $ \g' -> g' {
      thTerms = thTerms g' Q.|> HTermData name bis ty,
      thTermIx = M.insert name n (thTermIx g'),
      thDefs = I.insert (ofTermID n) (HDefData ds' def) (thDefs g') }
  trCmd (ProofThm x vs hs ret unf ds pf st) = do
    when st $ step >> return ()
    g <- get
    let n = ThmID (Q.length (thThms g))
    let name = fromMaybe (T.pack $ show n) x
    let (args, ty@(TType _ hs' ret'), ret2, p) =
          translateThm g vs hs ret (S.fromList unf) ds pf
    tell (Endo (HDThm name ty (Just p) :))
    modify $ \g' -> g' {thThms = thThms g' Q.|> HThmData name args hs' ret' ret2}
  trCmd (StepInout _) = step >>= \case
    SInout _ -> return ()
    _ -> throwError "incorrect i/o step"

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

trGExpr :: ToHolState -> M.Map Ident PBinder -> [PBinder] -> SExpr -> GType
trGExpr g ctx bis = uclose bis . trExpr g ctx

trExpr :: ToHolState -> M.Map Ident PBinder -> SExpr -> Term
trExpr g ctx = trExpr' where
  trExpr' (SVar v) = case ctx M.! v of
    PBound _ _ -> LVar v
    PReg _ (DepType _ xs) -> RVar v xs
  trExpr' (App t es) =
    let HTermData _ bis ty = Q.index (thTerms g) (ofTermID (thTermIx g M.! t))
        (ls, xs) = trApp ty bis es in HApp t ls xs

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

trVBinders :: ToHolState -> [VBinder] -> ([(Ident, SType)], Int, Q.Seq PBinder)
trVBinders g = go 0 Q.empty where
  go n m [] = ([], n, m)
  go n m (VBound t : bis) =
    go (n+1) (m Q.|> PBound (varName (VarID n)) (thSort g t)) bis
  go n m (VReg t ts : bis) =
    let {
      v = varName (VarID n); t' = thSort g t;
      (rs', n', m') = go (n+1) (m Q.|> PReg v (DepType t' (varName <$> ts))) bis } in
    ((v, SType (snd . getVLocal m <$> ts) t') : rs', n', m')

getVLocal :: Q.Seq PBinder -> VarID -> (Ident, Sort)
getVLocal m (VarID n) = case Q.index m n of
  PBound x t -> (x, t)
  PReg _ _ -> error "not a bound variable"

translateDef :: ToHolState -> [VBinder] -> VType -> [SortID] -> VExpr ->
  ([PBinder], DepType, [(Ident, SType)], [(Ident, Sort)], Sort, Term, [(Ident, Sort)])
translateDef g  = \vs (VType t ts) ds e ->
  let (rs, n, ctx) = trVBinders g vs
      t' = thSort g t
      ls = getVLocal ctx <$> ts
      (_, ctx', ds') = trDummies n ctx ds in
  (toList ctx, DepType t' (fst <$> ls), rs, ls, t', trVExpr g ctx' e, ds')
  where

  trDummies :: Int -> Q.Seq PBinder -> [SortID] -> (Int, Q.Seq PBinder, [(Ident, Sort)])
  trDummies n ctx [] = (n, ctx, [])
  trDummies n ctx (d:ds) =
    let { x = varName (VarID n); s = thSort g d;
          (n', ctx', bs') = trDummies (n+1) (ctx Q.|> PBound x s) ds } in
    (n', ctx', (x, s) : bs')

trVSExpr :: ToHolState -> Q.Seq PBinder -> VExpr -> SExpr
trVSExpr g ctx = go where
  go (VVar (VarID n)) = SVar (binderName (Q.index ctx n))
  go (VApp t es) = App (htName (thTerm g t)) (go <$> es)

trVExpr :: ToHolState -> Q.Seq PBinder -> VExpr -> Term
trVExpr g ctx = trVExpr' where
  trVExpr' (VVar (VarID n)) = case Q.index ctx n of
    PBound x _ -> LVar x
    PReg x (DepType _ ts) -> RVar x ts
  trVExpr' (VApp t es) =
    let HTermData x bis ty = thTerm g t
        (ls, xs) = trApp ty bis es in HApp x ls xs

  trApp :: DepType -> [PBinder] -> [VExpr] -> ([SLam], [Ident])
  trApp (DepType _ ts) = go M.empty where
    go :: M.Map Ident (Ident, Sort) -> [PBinder] -> [VExpr] -> ([SLam], [Ident])
    go m [] [] = ([], fst . (m M.!) <$> ts) -- TODO: test this
    go m (PBound x t : bis) (VVar e : es) = go (M.insert x (varName e, t) m) bis es
    go _ (PBound _ _ : _) (_ : _) = error "bad proof"
    go m (PReg _ (DepType _ ts') : bis) (e : es) =
      let (ls, xs) = go m bis es in
      (SLam ((m M.!) <$> ts') (trVExpr' e) : ls, xs)
    go _ _ _ = error "incorrect number of arguments"

trVGExpr :: ToHolState -> Q.Seq PBinder -> [PBinder] -> VExpr -> GType
trVGExpr g ctx bis = uclose bis . trVExpr g ctx

translateThm :: ToHolState -> [VBinder] -> [VExpr] -> VExpr -> S.Set TermID ->
  [SortID] -> ProofTree -> ([PBinder], TType, SExpr, ([Ident], HProof))
translateThm g vs hs ret unf ds pf =
  let (rs, _, ctx) = trVBinders g vs
      args = toList ctx
      hs' = trVGExpr g ctx args <$> hs
      ret' = trVGExpr g ctx args ret
      ret2 = trVSExpr g ctx ret
      ty = TType rs hs' ret'
      ((uehs, uer), ctx') = ST.runState
        (liftM2 (,) (mapM (unfoldExpr g unf) hs) (unfoldExpr g unf ret)) ctx
      proof = do
        ns <- mkHeap uehs hs'
        addDummies (thSort g <$> ds)
        (\(HProofF _ p _) -> (ns, convRet (ueConv uer) p)) <$> trProof g pf
      initSt = (varToSlot <$> ctx', foldl mkVars M.empty ctx', M.empty)
  in (args, ty, ret2, ST.evalState proof initSt)

data HSlot =
    HExpr (S.Set Ident) Term
  | HProof (ToHolProofM (S.Set Ident, HProof, Term))

type ToHolProofM = ST.State (Q.Seq HSlot, M.Map Ident Sort, M.Map Ident GType)

varToSlot :: PBinder -> HSlot
varToSlot (PBound v _) = HExpr (S.singleton v) (LVar v)
varToSlot (PReg v (DepType _ vs)) = HExpr (S.fromList vs) (RVar v vs)

mkVars :: M.Map Ident Sort -> PBinder -> M.Map Ident Sort
mkVars m (PBound v s) = M.insert v s m
mkVars m _ = m

data HSlotF =
    HExprF (S.Set Ident) Term
  | HProofF (S.Set Ident) HProof Term

forceSlot :: HSlot -> ToHolProofM HSlotF
forceSlot (HExpr vs e) = return $ HExprF vs e
forceSlot (HProof m) = (\(vs, p, t) -> HProofF vs p t) <$> m

instance Show HSlot where
  show (HExpr _ e) = "HExpr " ++ show e
  show (HProof _) = "HProof <suspended>"

instance Show HSlotF where
  show (HExprF _ e) = "HExpr " ++ show e
  show (HProofF _ _ t) = "HProof of " ++ show t

substVExpr :: ToHolState -> Q.Seq (VExpr, Term) -> VExpr -> (VExpr, Term)
substVExpr g subst = substVExpr' where
  substVExpr' (VVar (VarID n)) = Q.index subst n
  substVExpr' (VApp t es) =
    let HTermData x bis ty = thTerm g t
        (es', ls, xs) = substApp ty bis es in (VApp t es', HApp x ls xs)

  substApp :: DepType -> [PBinder] -> [VExpr] -> ([VExpr], [SLam], [Ident])
  substApp (DepType _ ts) = go M.empty where
    go :: M.Map Ident ((Ident, Sort), VarID) -> [PBinder] -> [VExpr] -> ([VExpr], [SLam], [Ident])
    go m [] [] = ([], [], varName . snd . (m M.!) <$> ts)
    go m (PBound x t : bis) (VVar e : es) =
      let (y, LVar z) = Q.index subst (ofVarID e)
          (es', ls, xs) = go (M.insert x ((z, t), e) m) bis es in
      (y : es', ls, xs)
    go _ (PBound _ _ : _) (_ : _) = error "bad proof"
    go m (PReg _ (DepType _ ts') : bis) (e : es) =
      let (e', t') = substVExpr' e
          (es', ls, xs) = go m bis es in
      (e' : es', SLam (fst . (m M.!) <$> ts') t' : ls, xs)
    go _ _ _ = error "incorrect number of arguments"

data UnfoldExpr = UnfoldExpr {
  ueVExpr :: VExpr,
  ueConv :: HConv,
  ueLHS :: Term,
  ueRHS :: Term }

reflTerm :: HConv -> Maybe Term
reflTerm (CRefl e) = Just e
reflTerm _ = Nothing

reflLam :: HConvLam -> Maybe SLam
reflLam (HConvLam vs c) = SLam vs <$> reflTerm c

buildSubst :: Q.Seq (VExpr, Term) -> [(Ident, Sort)] -> ST.State (Q.Seq PBinder) (Q.Seq (VExpr, Term))
buildSubst m [] = return m
buildSubst m ((_, d) : ds) = do
  ctx <- get
  let v = VarID (Q.length ctx)
  modify (Q.|> PBound (varName v) d)
  buildSubst (m Q.|> (VVar v, LVar (varName v))) ds

unfoldExpr :: ToHolState -> S.Set TermID -> VExpr -> ST.State (Q.Seq PBinder) UnfoldExpr
unfoldExpr g unf = unfoldExpr' where
  unfoldExpr' (VApp t es) = do
    let HTermData x bis ty = thTerm g t
    (es', cs, ls, rs, xs) <- unfoldApp ty bis es
    let t1 = HApp x ls xs
    if S.member t unf then do
      let HDefData ud uv = thDefs g I.! ofTermID t
      subst <- buildSubst (Q.fromList es') ud
      let (e', t2) = substVExpr g subst uv
      let c = CDef x rs xs
      return $ case mapM reflLam cs of
        Nothing -> UnfoldExpr e' (CTrans (CCong x cs xs) c) t1 t2
        Just _ -> UnfoldExpr e' c t1 t2
    else
      return $ case mapM reflLam cs of
        Nothing -> UnfoldExpr (VApp t (fst <$> es')) (CCong x cs xs) t1 (HApp x rs xs)
        Just _ -> UnfoldExpr (VApp t es) (CRefl t1) t1 t1
  unfoldExpr' e = do
    ctx <- get
    let t = trVExpr g ctx e
    return $ UnfoldExpr e (CRefl t) t t

  unfoldApp :: DepType -> [PBinder] -> [VExpr] ->
    ST.State (Q.Seq PBinder) ([(VExpr, Term)], [HConvLam], [SLam], [SLam], [Ident])
  unfoldApp (DepType _ ts) = go M.empty where
    go :: M.Map Ident (Ident, Sort) -> [PBinder] -> [VExpr] ->
      ST.State (Q.Seq PBinder) ([(VExpr, Term)], [HConvLam], [SLam], [SLam], [Ident])
    go m [] [] = return ([], [], [], [], T.pack . show . snd . (m M.!) <$> ts)
    go m (PBound x t : bis) (VVar e : es) = do
      (es', cs, ls, rs, xs) <- go (M.insert x (varName e, t) m) bis es
      return ((VVar e, LVar (varName e)) : es', cs, ls, rs, xs)
    go _ (PBound _ _ : _) (_ : _) = error "bad proof"
    go m (PReg _ (DepType _ ts') : bis) (e : es) = do
      UnfoldExpr e' c l r <- unfoldExpr' e
      (es', cs, ls, rs, xs) <- go m bis es
      let vs = (m M.!) <$> ts'
      return ((e', l) : es', HConvLam vs c : cs, SLam vs l : ls, SLam vs r : rs, xs)
    go _ _ _ = error "incorrect number of arguments"

mkHeap :: [UnfoldExpr] -> [GType] -> ToHolProofM [Ident]
mkHeap [] [] = return []
mkHeap (UnfoldExpr _ c _ t : ues) (h@(GType xs _) : hs) = do
  (ctx, m, heap) <- get
  let n = Q.length ctx
      v = varName (VarID n)
      p = HHyp v (fst <$> xs)
      p' = case reflTerm c of
        Just _ -> return (fvLTerm t, p, t)
        Nothing -> save n (v <> "_unf") xs (HConv c p) t
  put (ctx Q.|> HProof p', m, M.insert v h heap)
  (v :) <$> mkHeap ues hs
mkHeap _ _ = error "incorrect number of arguments"

save :: Int -> Ident -> [(Ident, Sort)] -> HProof -> Term ->
  ToHolProofM (S.Set Ident, HProof, Term)
save n x vs p t = do
  let fv = fvLTerm t
  modify $ \(ctx, m, heap) ->
    (Q.update n (HProof (return (fv, HHyp x (fst <$> vs), t))) ctx, m,
     M.insert x (GType vs t) heap)
  return (fv, HSave x (HProofLam vs p) (fst <$> vs), t)

convRet :: HConv -> HProof -> HProof
convRet c = case reflTerm c of
  Just _ -> id
  Nothing -> HConv (CSymm c)

addDummies :: [Sort] -> ToHolProofM ()
addDummies = \ds -> modify $ \(ctx, vs, heap) -> go (Q.length ctx) ds ctx vs heap where
  go _ [] ctx vs heap = (ctx, vs, heap)
  go n (d:ds) ctx vs heap =
    let v = varName (VarID n) in
    go (n+1) ds (ctx Q.|> HExpr (S.singleton v) (LVar v)) (M.insert v d vs) heap

substSExpr :: ToHolState -> M.Map Ident Term -> SExpr -> Term
substSExpr g subst = substSExpr' where
  substSExpr' (SVar v) = subst M.! v
  substSExpr' (App t es) =
    let HTermData x bis ty = thTerm g (thTermIx g M.! t)
        (ls, xs) = substApp ty bis es in HApp x ls xs

  substApp :: DepType -> [PBinder] -> [SExpr] -> ([SLam], [Ident])
  substApp (DepType _ ts) = go M.empty where
    go :: M.Map Ident (Ident, Sort) -> [PBinder] -> [SExpr] -> ([SLam], [Ident])
    go m [] [] = ([], fst . (m M.!) <$> ts)
    go m (PBound x t : bis) (SVar v : es) =
      let LVar z = subst M.! v
          (ls, xs) = go (M.insert x (z, t) m) bis es in
      (ls, xs)
    go _ (PBound _ _ : _) (_ : _) = error "bad proof"
    go m (PReg _ (DepType _ ts') : bis) (e : es) =
      let t' = substSExpr' e
          (ls, xs) = go m bis es in
      (SLam ((m M.!) <$> ts') t' : ls, xs)
    go _ _ _ = error "incorrect number of arguments"

trLoad :: HeapID -> ToHolProofM HSlotF
trLoad (VarID n) = get >>= \(ctx, _, _) -> forceSlot $ Q.index ctx n

type TrThm = (S.Set Ident, M.Map Ident SLam, M.Map Ident Term, [SLam], [HProofLam], [Ident])

trProof :: ToHolState -> ProofTree -> ToHolProofM HSlotF
trProof g pr = trProof' pr where
  trProof' :: ProofTree -> ToHolProofM HSlotF
  trProof' (Load n) = trLoad n
  trProof' (VTerm t ps) = do
    let HTermData x bis ty = thTerm g t
    (fv, ls, xs) <- trApp ty bis ps
    return $ HExprF fv $ HApp x ls xs
  trProof' (VThm t ps) = do
    let HThmData x bis hs ret ret' = thThm g t
    (fv, _, subst, ls, ps', xs) <- trThm hs ret bis ps
    let ty = substSExpr g subst ret'
    let fv' = fvLTerm ty
    let p = HThm x ls ps' xs
    if S.size fv == S.size fv' then
      return $ HProofF fv' p ty
    else do
      let ds = S.toList (S.difference fv fv')
      (_, m, _) <- get
      return $ HProofF fv' (HForget ty (HProofLam ((\d -> (d, m M.! d)) <$> ds) p)) ty

  trProof' (Save p) = trProof' p >>= \case
    HExprF fv e -> do
      modify $ \(ctx, m, heap) -> (ctx Q.|> HExpr fv e, m, heap)
      return (HExprF fv e)
    HProofF fv p' t -> do
      (ctx, m, heap) <- get
      let x = varName (VarID (Q.length ctx))
      put (ctx Q.|> HProof (return (fv, HHyp x [], t)), m, M.insert x (GType [] t) heap)
      return $ HProofF fv (HSave x (HProofLam [] p') []) t
  trProof' Sorry = return $ HProofF S.empty HSorry HTSorry

  trPTExpr :: ProofTree -> ToHolProofM (S.Set Ident, Term)
  trPTExpr p = trProof' p >>= \case
    HExprF s e -> return (s, e)
    _ -> return (S.empty, HTSorry)

  trApp :: DepType -> [PBinder] -> [ProofTree] -> ToHolProofM (S.Set Ident, [SLam], [Ident])
  trApp (DepType _ ts) = go M.empty S.empty where
    go :: M.Map Ident (Ident, Sort) -> S.Set Ident ->
      [PBinder] -> [ProofTree] -> ToHolProofM (S.Set Ident, [SLam], [Ident])
    go m s [] [] = let ls = fst . (m M.!) <$> ts in
      return (s <> S.fromList ls, [], ls)
    go m s (PBound x t : bis) (Load e : es) =
      trLoad e >>= \(HExprF _ (LVar v)) ->
        go (M.insert x (v, t) m) s bis es
    go _ _ (PBound _ _ : _) (_ : _) = error "bad proof"
    go m s (PReg _ (DepType _ ts') : bis) (e : es) = do
      (fv, e') <- trPTExpr e
      let xts = (m M.!) <$> ts'
      (s', ls, xs) <- go m (s <> foldr S.delete fv (fst <$> xts)) bis es
      return (s', SLam xts e' : ls, xs)
    go _ _ _ _ = error "incorrect number of arguments"

  trThm :: [GType] -> GType -> [PBinder] -> [ProofTree] -> ToHolProofM TrThm
  trThm hs (GType rv _) = trThmArgs M.empty S.empty M.empty M.empty id where
    trThmArgs :: M.Map Ident (Ident, Sort) -> S.Set Ident -> M.Map Ident SLam ->
      M.Map Ident Term -> ([SLam] -> [SLam]) -> [PBinder] -> [ProofTree] -> ToHolProofM TrThm
    trThmArgs m s es q f [] ps = trThmHyps (f []) m s es q hs ps
    trThmArgs m s es q f (PBound x t : bis) (Load e : ps) =
      trLoad e >>= \(HExprF _ (LVar v)) ->
        trThmArgs (M.insert x (v, t) m) s es (M.insert x (LVar v) q) f bis ps
    trThmArgs _ _ _ _ _ (PBound _ _ : _) (_ : _) = error "bad proof"
    trThmArgs m s es q f (PReg v (DepType _ ts) : bis) (p : ps) = do
      (fv, e') <- trPTExpr p
      let xts = (m M.!) <$> ts
      let l = SLam xts e'
      trThmArgs m (s <> foldr S.delete fv (fst <$> xts))
        (M.insert v l es) (M.insert v e' q) (f . (l :)) bis ps
    trThmArgs _ _ _ _ _ _ _ = error "incorrect number of arguments"

    trThmHyps :: [SLam] -> M.Map Ident (Ident, Sort) -> S.Set Ident -> M.Map Ident SLam ->
      M.Map Ident Term -> [GType] -> [ProofTree] -> ToHolProofM TrThm
    trThmHyps ls m s es q = go id where
      go :: ([HProofLam] -> [HProofLam]) -> [GType] -> [ProofTree] -> ToHolProofM TrThm
      go f [] [] = let xs = fst . (m M.!) . fst <$> rv in
        return (s <> S.fromList xs, es, q, ls, f [], xs)
      go f (GType hv _ : hs') (p : ps) =
        trProof' p >>= \case
         HProofF _ p' _ -> go (f . (HProofLam ((m M.!) . fst <$> hv) p' :)) hs' ps
         HExprF _ _ -> error "bad stack slot"
      go _ _ _ = error "incorrect number of arguments"
