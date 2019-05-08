{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ToHol where

import Control.Monad.Except
import Control.Monad.RWS.Strict hiding (liftIO)
import Data.Maybe
import Data.Foldable
import qualified Control.Monad.Trans.State as ST
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Q
import qualified Data.IntMap as I
import qualified Data.Set as S
import HolTypes
import Environment
import ProofTypes
import Util

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
  haRet :: GType }          -- ^ Conclusion

data ToHolState = ToHolState {
  thPos :: Int,
  thSorts :: Q.Seq (Sort, Bool),
  thSortIx :: M.Map Ident SortID,
  thTerms :: Q.Seq HTermData,
  thTermIx :: M.Map Ident TermID,
  thThms :: Q.Seq HThmData,
  thDefs :: I.IntMap HDefData
   }

thSort :: ToHolState -> SortID -> Sort
thSort g (SortID n) = fst (Q.index (thSorts g) n)

thTerm :: ToHolState -> TermID -> HTermData
thTerm g (TermID n) = Q.index (thTerms g) n

thThm :: ToHolState -> ThmID -> HThmData
thThm g (ThmID n) = Q.index (thThms g) n

type ToHolM = RWST () (Endo [HDecl]) ToHolState (Either String)

toHol :: Environment -> Proofs -> Either String [HDecl]
toHol env = \pfs -> do
  (_, st, Endo f) <- runRWST (mapM_ trCmd pfs) () $
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
    e -> throwError ("incorrect step 'sort " ++ x ++ "', found " ++ show e)
  trCmd (StepTerm x) = step >>= \case
    SDecl x' (DTerm args ty) | x == x' -> do
      tell (Endo (HDTerm x (translateTerm args ty) :))
      modify $ \g -> g {
        thTerms = thTerms g Q.|> HTermData x args ty,
        thTermIx = M.insert x (TermID (Q.length (thTerms g))) (thTermIx g) }
    e -> throwError ("incorrect step 'term " ++ x ++ "', found " ++ show e)
  trCmd (StepAxiom x) = step >>= \case
    SDecl x' (DAxiom args hs ret) | x == x' -> do
      g <- get
      let td@(TType _ hs' ret') = translateAxiom g args hs ret
      tell (Endo (HDThm x td Nothing :))
      put $ g {thThms = thThms g Q.|> HThmData x args hs' ret'}
    e -> throwError ("incorrect step 'axiom " ++ x ++ "', found " ++ show e)
  trCmd (ProofDef x vs ret ds def st) = do
    when st $ step >> return ()
    g <- get
    let n = TermID (Q.length (thTerms g))
    let name = fromMaybe (show n) x
    let (bis, ty, rv, lv, r, e, ds') = translateDef g vs ret ds def
    tell (Endo (HDDef name rv lv e :))
    modify $ \g -> g {
      thTerms = thTerms g Q.|> HTermData name bis ty,
      thTermIx = M.insert name n (thTermIx g),
      thDefs = I.insert (ofTermID n) (HDefData ds' def) (thDefs g) }
  trCmd (ProofThm x vs hs ret unf ds pf st) = do
    when st $ step >> return ()
    g <- get
    let n = ThmID (Q.length (thThms g))
    let name = fromMaybe (show n) x
    let (args, ty@(TType _ hs' ret'), p) =
          translateThm g vs hs ret (S.fromList unf) ds pf
    tell (Endo (HDThm name ty (Just p) :))
    modify $ \g -> g {thThms = thThms g Q.|> HThmData name args hs' ret'}
  trCmd (StepInout _) = step >>= \case
    SInout _ -> return ()
    _ -> throwError "incorrect i/o step"

getLocal :: M.Map Ident PBinder -> Ident -> Sort
getLocal m v = case m M.! v of PBound _ t -> t

trBinders :: [PBinder] -> ([(Ident, SType)], M.Map Ident PBinder)
trBinders = go M.empty where
  go m [] = ([], m)
  go m (p@(PBound v t) : bis) = go (M.insert v p m) bis
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

fvLam :: SLam -> S.Set Ident
fvLam (SLam vs t) = foldr S.delete (fvTerm t) (fst <$> vs)

fvTerm :: Term -> S.Set Ident
fvTerm (LVar x) = S.singleton x
fvTerm (RVar _ xs) = S.fromList xs
fvTerm (HApp _ ls xs) = foldMap fvLam ls <> S.fromList xs

fvBind :: [PBinder] -> Term -> [(Ident, Sort)]
fvBind vs t = mapMaybe g vs where
  fvs = fvTerm t
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
    go :: M.Map Ident (Sort, Ident) -> [PBinder] -> [SExpr] -> ([SLam], [Ident])
    go m [] [] = ([], snd . (m M.!) <$> ts)
    go m (PBound x t : bis) (SVar e : es) = go (M.insert x (t, e) m) bis es
    go m (PReg v (DepType t ts) : bis) (e : es) =
      let (ls, xs) = go m bis es in
      (SLam ((\x -> (x, fst $ m M.! x)) <$> ts) (trExpr' e) : ls, xs)

trVBinders :: ToHolState -> [VBinder] -> ([(Ident, SType)], Int, Q.Seq PBinder)
trVBinders g = go 0 Q.empty where
  go n m [] = ([], n, m)
  go n m (p@(VBound t) : bis) =
    go (n+1) (m Q.|> PBound (show (VarID n)) (thSort g t)) bis
  go n m (p@(VReg t ts) : bis) =
    let {
      v = show (VarID n); t' = thSort g t;
      (rs', n', m') = go (n+1) (m Q.|> PReg v (DepType t' (show <$> ts))) bis } in
    ((v, SType (snd . getVLocal m <$> ts) t') : rs', n', m')

getVLocal :: Q.Seq PBinder -> VarID -> (Ident, Sort)
getVLocal m (VarID n) = case Q.index m n of PBound x t -> (x, t)

translateDef :: ToHolState -> [VBinder] -> VType -> [SortID] -> VExpr ->
  ([PBinder], DepType, [(Ident, SType)], [(Ident, Sort)], Sort, Term, [(Ident, Sort)])
translateDef g vs (VType t ts) ds e =
  let (rs, n, ctx) = trVBinders g vs
      t' = thSort g t
      ls = getVLocal ctx <$> ts
      (n', ctx', ds') = trDummies n ctx ds in
  (toList ctx, DepType t' (fst <$> ls), rs, ls, t', trVExpr g ctx' e, ds')
  where

  trDummies :: Int -> Q.Seq PBinder -> [SortID] -> (Int, Q.Seq PBinder, [(Ident, Sort)])
  trDummies n ctx [] = (n, ctx, [])
  trDummies n ctx (d:ds) =
    let { x = show (VarID n); s = thSort g d;
          (n', ctx', bs') = trDummies (n+1) (ctx Q.|> PBound x s) ds } in
    (n', ctx', (x, s) : bs')

trVExpr :: ToHolState -> Q.Seq PBinder -> VExpr -> Term
trVExpr g ctx = trVExpr' where
  trVExpr' (VVar (VarID n)) = case Q.index ctx n of
    PBound x s -> LVar x
    PReg x (DepType t ts) -> RVar x ts
  trVExpr' (VApp t es) =
    let HTermData x bis ty = thTerm g t
        (ls, xs) = trApp ty bis es in HApp x ls xs

  trApp :: DepType -> [PBinder] -> [VExpr] -> ([SLam], [Ident])
  trApp (DepType _ ts) = go M.empty where
    go :: M.Map Ident (Ident, Sort) -> [PBinder] -> [VExpr] -> ([SLam], [Ident])
    go m [] [] = ([], show . snd . (m M.!) <$> ts)
    go m (PBound x t : bis) (VVar e : es) = go (M.insert x (show e, t) m) bis es
    go m (PReg v (DepType t ts) : bis) (e : es) =
      let (ls, xs) = go m bis es in
      (SLam ((m M.!) <$> ts) (trVExpr' e) : ls, xs)

trVGExpr :: ToHolState -> Q.Seq PBinder -> [PBinder] -> VExpr -> GType
trVGExpr g ctx bis = uclose bis . trVExpr g ctx

translateThm :: ToHolState -> [VBinder] -> [VExpr] -> VExpr -> S.Set TermID ->
  [SortID] -> ProofTree -> ([PBinder], TType, ([Ident], HProof))
translateThm g vs hs ret unf ds pf =
  let (rs, n, ctx) = trVBinders g vs
      args = toList ctx
      hs' = trVGExpr g ctx args <$> hs
      ret' = trVGExpr g ctx args ret
      ty = TType rs hs' ret'
      ((uehs, uer), ctx') = ST.runState
        (liftM2 (,) (mapM (unfoldExpr g unf) hs) (unfoldExpr g unf ret)) ctx
      proof = do
        ns <- mkHeap uehs hs'
        addDummies (thSort g <$> ds)
        (\(HProofF p _) -> (ns, convRet (ueConv uer) p)) <$> trProof g pf
  in (args, ty, ST.evalState proof (varToSlot <$> ctx, M.empty))

data HSlot = HExpr Term | HProof (ToHolProofM (HProof, Term))

type ToHolProofM = ST.State (Q.Seq HSlot, M.Map Ident GType)

varToSlot :: PBinder -> HSlot
varToSlot (PBound v _) = HExpr (LVar v)
varToSlot (PReg v (DepType _ vs)) = HExpr (RVar v vs)

data HSlotF = HExprF Term | HProofF HProof Term

forceSlot :: HSlot -> ToHolProofM HSlotF
forceSlot (HExpr e) = return $ HExprF e
forceSlot (HProof m) = (\(p, t) -> HProofF p t) <$> m

substVExpr :: ToHolState -> Q.Seq (VExpr, Term) -> VExpr -> (VExpr, Term)
substVExpr g subst = substVExpr' where
  substVExpr' (VVar (VarID n)) = Q.index subst n
  substVExpr' (VApp t es) =
    let HTermData x bis ty = thTerm g t
        (es', ls, xs) = substApp ty bis es in (VApp t es', HApp x ls xs)

  substApp :: DepType -> [PBinder] -> [VExpr] -> ([VExpr], [SLam], [Ident])
  substApp (DepType _ ts) = go M.empty where
    go :: M.Map Ident ((Ident, Sort), VarID) -> [PBinder] -> [VExpr] -> ([VExpr], [SLam], [Ident])
    go m [] [] = ([], [], show . snd . (m M.!) <$> ts)
    go m (PBound x t : bis) (VVar e : es) =
      let (y, LVar z) = Q.index subst (ofVarID e)
          (es', ls, xs) = go (M.insert x ((z, t), e) m) bis es in
      (y : es', ls, xs)
    go m (PReg v (DepType t ts) : bis) (e : es) =
      let (e', t') = substVExpr' e
          (es', ls, xs) = go m bis es in
      (e' : es', SLam (fst . (m M.!) <$> ts) t' : ls, xs)

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
  modify (Q.|> PBound (show v) d)
  buildSubst (m Q.|> (VVar v, LVar (show v))) ds

unfoldExpr :: ToHolState -> S.Set TermID -> VExpr -> ST.State (Q.Seq PBinder) UnfoldExpr
unfoldExpr g unf = unfoldExpr' where
  unfoldExpr' (VApp t es) = do
    let HTermData x bis ty@(DepType s _) = thTerm g t
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
        Just es'' -> UnfoldExpr (VApp t es) (CRefl t1) t1 t1
  unfoldExpr' e = do
    ctx <- get
    let t = trVExpr g ctx e
    return $ UnfoldExpr e (CRefl t) t t

  unfoldApp :: DepType -> [PBinder] -> [VExpr] ->
    ST.State (Q.Seq PBinder) ([(VExpr, Term)], [HConvLam], [SLam], [SLam], [Ident])
  unfoldApp (DepType _ ts) = go M.empty where
    go :: M.Map Ident (Ident, Sort) -> [PBinder] -> [VExpr] ->
      ST.State (Q.Seq PBinder) ([(VExpr, Term)], [HConvLam], [SLam], [SLam], [Ident])
    go m [] [] = return ([], [], [], [], show . snd . (m M.!) <$> ts)
    go m (PBound x t : bis) (VVar e : es) = do
      (es', cs, ls, rs, xs) <- go (M.insert x (show e, t) m) bis es
      return ((VVar e, LVar (show e)) : es', cs, ls, rs, xs)
    go m (PReg v (DepType t ts) : bis) (e : es) = do
      UnfoldExpr e' c l r <- unfoldExpr' e
      (es', cs, ls, rs, xs) <- go m bis es
      let vs = (m M.!) <$> ts
      return ((e', l) : es', HConvLam vs c : cs, SLam vs l : ls, SLam vs r : rs, xs)

mkHeap :: [UnfoldExpr] -> [GType] -> ToHolProofM [Ident]
mkHeap [] [] = return []
mkHeap (UnfoldExpr e c t1 t2 : ues) (h@(GType xs t) : hs) = do
  (ctx, heap) <- get
  let n = Q.length ctx
      v = show (VarID n)
      p = HHyp v (fst <$> xs)
      p' = case reflTerm c of
        Just _ -> return (p, t2)
        Nothing -> save n (v ++ "_unf") xs (HConv c p) t2
  put (ctx Q.|> HProof p', M.insert v h heap)
  (v :) <$> mkHeap ues hs
  where

  save :: Int -> Ident -> [(Ident, Sort)] -> HProof -> Term -> ToHolProofM (HProof, Term)
  save n x vs p t = do
    modify $ \(ctx, heap) ->
      (Q.update n (HProof (return (HHyp x (fst <$> vs), t))) ctx,
       M.insert x (GType vs t) heap)
    return (HSave x (HProofLam vs p) (fst <$> vs), t)

convRet :: HConv -> HProof -> HProof
convRet c = case reflTerm c of
  Just _ -> id
  Nothing -> HConv (CSymm c)

addDummies :: [Sort] -> ToHolProofM ()
addDummies ds = modify $ \(ctx, heap) -> (go (Q.length ctx) ds ctx, heap) where
  go _ [] ctx = ctx
  go n (d:ds) ctx = go (n+1) ds (ctx Q.|> HExpr (LVar (show (VarID n))))

trLoad :: HeapID -> ToHolProofM HSlotF
trLoad (VarID n) = get >>= \(ctx, _) -> forceSlot $ Q.index ctx n

trProof :: ToHolState -> ProofTree -> ToHolProofM HSlotF
trProof g pr = trProof' pr where
  trProof' :: ProofTree -> ToHolProofM HSlotF
  trProof' (Load n) = trLoad n
  trProof' (VTerm t ps) = do
    let HTermData x bis ty = thTerm g t
    (ls, xs) <- trApp ty bis ps
    return $ HExprF $ HApp x ls xs
  trProof' (VThm t ps) = do
    let HThmData x bis hs ret@(GType ss r) = thThm g t
    (ls, ps', xs) <- trThm hs ret bis ps
    let ty = vsubstTerm (M.fromList (zip (fst <$> ss) xs)) r
    return $ HProofF (HThm x ls ps' xs) ty
  trProof' (Save p) = trProof' p >>= \case
    HExprF e -> do
      modify $ \(ctx, heap) -> (ctx Q.|> HExpr e, heap)
      return (HExprF e)
    HProofF p' t -> do
      (ctx, heap) <- get
      let x = show (VarID (Q.length ctx))
      put (ctx Q.|> HProof (return (HHyp x [], t)), M.insert x (GType [] t) heap)
      return $ HProofF (HSave x (HProofLam [] p') []) t
  trProof' Sorry = return $ HProofF HSorry HTSorry

  trPTExpr :: ProofTree -> ToHolProofM Term
  trPTExpr p = trProof' p >>= \case
    HExprF e -> return e
    _ -> return HTSorry

  trApp :: DepType -> [PBinder] -> [ProofTree] -> ToHolProofM ([SLam], [Ident])
  trApp (DepType _ ts) = go M.empty where
    go :: M.Map Ident (Ident, Sort) -> [PBinder] -> [ProofTree] -> ToHolProofM ([SLam], [Ident])
    go m [] [] = return ([], show . snd . (m M.!) <$> ts)
    go m (PBound x t : bis) (Load e : es) =
      trLoad e >>= \(HExprF (LVar v)) ->
        go (M.insert x (v, t) m) bis es
    go m (PReg v (DepType t ts) : bis) (e : es) = do
      e' <- trPTExpr e
      (ls, xs) <- go m bis es
      return (SLam ((m M.!) <$> ts) e' : ls, xs)

  trThm :: [GType] -> GType -> [PBinder] -> [ProofTree] ->
    ToHolProofM ([SLam], [HProofLam], [Ident])
  trThm hs (GType rv ret) = trThmArgs M.empty id where
    trThmArgs :: M.Map Ident (Ident, Sort) -> ([SLam] -> [SLam]) ->
      [PBinder] -> [ProofTree] -> ToHolProofM ([SLam], [HProofLam], [Ident])
    trThmArgs m f [] ps = trThmHyps (f []) m hs ps
    trThmArgs m f (PBound x t : bis) (Load e : ps) =
      trLoad e >>= \(HExprF (LVar v)) ->
        trThmArgs (M.insert x (v, t) m) f bis ps
    trThmArgs m f (PReg v (DepType t ts) : bis) (p : ps) = do
      e' <- trPTExpr p
      trThmArgs m (f . (SLam ((m M.!) <$> ts) e' :)) bis ps

    trThmHyps :: [SLam] -> M.Map Ident (Ident, Sort) ->
      [GType] -> [ProofTree] -> ToHolProofM ([SLam], [HProofLam], [Ident])
    trThmHyps ls m = go id where
      go :: ([HProofLam] -> [HProofLam]) -> [GType] -> [ProofTree] ->
        ToHolProofM ([SLam], [HProofLam], [Ident])
      go f [] [] = return (ls, f [], fst . (m M.!) . fst <$> rv)
      go f (GType hv _ : hs) (p : ps) =
        trProof' p >>= \case
         HProofF p' t -> go (f . (HProofLam ((m M.!) . fst <$> hv) p' :)) hs ps
         HExprF e -> error ("error in translating proof: " ++ show pr ++
          "\n  at trThm " ++ show hs ++ " " ++ show (GType rv ret) ++
           "\n  so far " ++ show (f []) ++ "\n  got " ++ show p ++ " --> " ++ show e)
