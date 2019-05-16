module ToOpenTheory where

import GHC.Stack
import Control.Monad.RWS.Strict hiding (liftIO)
import qualified Control.Monad.Trans.State as ST
import qualified Data.Map.Strict as M
import Environment (Ident)
import HolTypes

data OTState = OTState {
  otDict :: Int,
  otArrow :: Maybe Int,
  otAll :: (Int, Int, Int, Int),
  otAllConst :: M.Map Sort Int,
  otSorts :: M.Map Ident Int,
  otEqs :: M.Map [Sort] Int,
  otTerms :: M.Map Ident Int,
  otDefs :: M.Map Ident ([(Ident, SType)], [(Ident, Sort)], Term, Int),
  otTypes :: M.Map SType Int,
  otVars :: M.Map (Ident, SType) Int,
  otThms :: M.Map Ident (TType, Int, [(Ident, Int)]),
  otHyps :: M.Map Ident (GType, [Int], Int),
  otHypApps :: M.Map (Ident, [Ident]) (Term, Int)
}

mkOTState :: OTState
mkOTState = OTState 0 Nothing undefined
  mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty

type OTM = RWS () (Endo [String]) OTState

otToString :: [HDecl] -> [String]
otToString ds = appEndo (snd $ evalRWS (preamble >> mapM_ otDecl ds) () mkOTState) []

emit :: [String] -> OTM ()
emit s = tell $ Endo (s ++)

ref :: Int -> OTM ()
ref n = app "ref" [emit [show n]]

ref' :: Int -> OTM Int
ref' n = ref n >> return n

def :: OTM Int
def = do
  g <- get
  let n = otDict g
  app "def" [emit [show n]]
  put $ g {otDict = n + 1}
  return n

save :: OTM Int
save = def <* emit ["pop"]

pushWith :: (OTState -> Maybe Int) -> (Int -> OTState -> OTState) -> OTM () -> OTM Int
pushWith r w go = do
  g <- get
  case r g of
    Just n -> ref' n
    Nothing -> do n <- go >> def; modify (w n); return n

pushSort :: Ident -> OTM Int
pushSort x = pushWith (\g -> otSorts g M.!? x)
  (\n g -> g {otSorts = M.insert x n (otSorts g)}) $ do
  app "opType" [app "typeOp" [str x], list []]

app :: String -> [OTM a] -> OTM ()
app s [] = emit [s]
app s (m:ms) = m >> app s ms

str :: String -> OTM ()
str s = emit [show s]

list :: [OTM a] -> OTM ()
list [] = emit ["nil"]
list (m:ms) = m >> list ms >> emit ["cons"]

(<!>) :: (HasCallStack, Ord k, Show k, Show v) => M.Map k v -> k -> v
(<!>) m k = case m M.!? k of
  Nothing -> error $ show m ++ " ! " ++ show k
  Just v -> v

preamble :: OTM ()
preamble = do
  app "version" [emit ["6"]]
  -- (
  str "OT.T" -- name OT.T
  let bool = pushSType (SType [] "bool")
  --   ( (
  app "constTerm" [
    app "const" [str "="],
    arrows [bool, bool] bool]
    -- = : bool -> bool -> bool
  idb <- pushVar "x" (SType [] "bool") >>
    def >>= ref >> emit ["varTerm", "absTerm"] >> def
    -- term \(x : bool), (x : bool)
  emit ["appTerm"]
  --     )
  ref idb
  e <- emit ["appTerm"] >> def -- term (\(x : bool), x) = (\(x : bool), x)
  --   )
  th <- emit ["defineConst", "sym"] >> save -- |- ((\x. x) = (\x. x)) = T
  ctru <- bool >> emit ["constTerm"] >> save -- T : bool
  -- )
  tru <- app "eqMp" [
    app "refl" [ref idb], -- |- (\(x : bool), x) = (\(x : bool), x)
    ref th] >> save -- |- T

  -- (
  str "OT.!" -- name OT.!
  --   (
  str "P"
  ab <- arrows [app "varType" [str "A"]] bool >> def -- type A -> bool
  p <- emit ["var"] >> def -- P : A -> bool
  --   )
  --   ( ( (
  app "constTerm" [app "const" [str "="],
    arrows [ref ab, ref ab] bool] -- = : (A -> bool) -> (A -> bool) -> bool
  pt <- app "varTerm" [ref p] >> def
  emit ["appTerm"] -- (=) P
  --       )
  --       (
  a <- app "var" [str "a", app "varType" [str "A"]] >> def -- a : A
  ref ctru
  lamt <- emit ["absTerm"] >> def -- \(a : A). T
  --       )
  emit ["appTerm"]
  --     )
  lam <- emit ["absTerm"] >> def -- \(P : A -> bool). (P = \(a : A). T)
  --   )
  emit ["defineConst"] -- |- ! = \(P : A -> bool). (P = \(a : A). T)
  -- )
  ap <- app "refl" [ref pt] >> emit ["appThm"] >> -- |- ! P = (\P. (P = \a. T)) P
    app "betaConv" [app "appTerm" [ref lam, ref pt]] >> emit ["trans"] >> save -- |- ! P = (P = \a. T)
  al <- def -- const !
  arrows [ref ab] bool >> emit ["constTerm"]
  ref pt >> emit ["appTerm", "assume"] -- {! P} |- ! P
  ref ap >> emit ["eqMp"] -- {! P} |- P = \a. T
  app "refl" [app "varTerm" [ref a]] >> emit ["appThm"] -- {! P} |- P a = (\a. T) a
  app "betaConv" [app "appTerm" [ref lamt, app "varTerm" [ref a]]] -- |- (\a. T) a = T
  emit ["trans", "sym"] -- {! P} |- T = P a
  alth <- ref tru >> emit ["eqMp"] >> save -- {! P} |- P a
  apr <- app "sym" [ref ap] >> save -- |- (P = \a. T) = ! P
  modify $ \g -> g {otAll = (al, tru, apr, alth)}

pushArrow :: OTM Int
pushArrow = pushWith otArrow (\n g -> g {otArrow = Just n}) $ do
  app "typeOp" [str "->"]

arrows :: [OTM a] -> OTM b -> OTM ()
arrows [] r = () <$ r
arrows (m : ms) r = app "opType" [
  () <$ pushArrow, list [() <$ m, () <$ arrows ms r]]

pushSType :: SType -> OTM Int
pushSType s@(SType ss t) = pushWith (\g -> otTypes g M.!? s)
  (\n g -> g {otTypes = M.insert s n (otTypes g)})
  (arrows (pushSort <$> ss) (pushSort t))

pushVar :: Ident -> SType -> OTM Int
pushVar x t = pushWith (\g -> otVars g M.!? (x, t))
  (\n g -> g {otVars = M.insert (x, t) n (otVars g)}) $ do
  app "var" [str x, () <$ pushSType t]

peekVar :: Ident -> SType -> OTM Int
peekVar x t = do
  g <- get
  case otVars g M.!? (x, t) of
    Just n -> return n
    Nothing -> pushVar x t <* emit ["pop"]

pushEq :: [Sort] -> OTM Int
pushEq ss = pushWith (\g -> otEqs g M.!? ss)
  (\n g -> g {otEqs = M.insert ss n (otEqs g)}) $
    let s = pushSType (SType ss "bool") in
    app "constTerm" [
      app "const" [str "="],
      arrows [s, s] (pushSType (SType [] "bool"))]

pushAllC :: Sort -> OTM Int
pushAllC s = pushWith (\g -> otAllConst g M.!? s)
  (\n g -> g {otAllConst = M.insert s n (otAllConst g)}) $
    app "constTerm" [
      do (n, _, _, _) <- otAll <$> get; ref n,
      arrows [pushSType (SType [s] "bool")] (pushSType (SType [] "bool"))]

-- pr: G |- ! (\x:s. t[x]), P := (\x:s. t[x]), a := a
-- pushes G |- t[a]
forallElim :: Sort -> OTM () -> OTM () -> OTM () -> OTM ()
forallElim s pr p a = app "proveHyp" [
  pr, -- G |- ! (\x:s. t[x])
  app "eqMp" [
    app "subst" [
      list [
        list [list [emit [show "A"], () <$ pushSType (SType [] s)]],
        list [list [emit [show "P"], p], list [emit [show "a"], a]]],
      do (_, _, _, n) <- otAll <$> get; ref n], -- {! P} |- (\x:s. t[x]) a
    app "betaConv" [app "appTerm" [p, a]]] -- {! P} |- t[a]
  ] -- G |- t[a]

-- pr: G |- t[x], var x : s, term t
-- pushes G |- ! (\x:s, t[x]), returns term (\x:s, t[x]), term ! (\x:s, t[x])
forallIntro :: Sort -> OTM () -> OTM () -> OTM () -> OTM (Int, OTM ())
forallIntro s x t pr = do
  (_, tru, apr, _) <- otAll <$> get
  l <- app "absTerm" [x, t] >> save
  app "eqMp" [
    app "absThm" [x, app "deductAntisym" [pr, ref tru]],
    app "subst" [
      list [
        list [list [emit [show "A"], () <$ pushSType (SType [] s)]],
        list [list [emit [show "P"], ref l]]],
      ref apr] -- |- ((\x:s. t[x]) = (\x:s. T)) = ! (\x:s. t[x])
    ] -- G |- ! (\x:s. t[x])
  return (l, app "appTerm" [() <$ pushAllC s, ref l])

pushAppVars :: M.Map Ident (OTM Int) -> OTM () -> [Ident] -> OTM ()
pushAppVars m f [] = f
pushAppVars m f (x:xs) =
  pushAppVars m (app "appTerm" [f, app "varTerm" [m M.! x]]) xs

pushAppLams :: M.Map Ident (OTM Int) -> OTM () -> [SLam] -> OTM ()
pushAppLams m f [] = f
pushAppLams m f (l:ls) =
  pushAppLams m (app "appTerm" [f, pushSLam m l]) ls

pushSLam :: M.Map Ident (OTM Int) -> SLam -> OTM ()
pushSLam m (SLam ss t) = go m ss where
  go :: M.Map Ident (OTM Int) -> [(Ident, Sort)] -> OTM ()
  go m [] = pushTerm m t
  go m ((x, s) : ss) = do
    n <- pushVar x (SType [] s)
    go (M.insert x (ref' n) m) ss
    emit ["absTerm"]

pushTerm :: M.Map Ident (OTM Int) -> Term -> OTM ()
pushTerm m (LVar x) = app "varTerm" [m M.! x]
pushTerm m (RVar v xs) = pushAppVars m (app "varTerm" [m M.! v]) xs
pushTerm m (HApp t ls xs) =
  pushAppVars m (pushAppLams m (get >>= ref . (<!> t) . otTerms) ls) xs

otDecl :: HDecl -> OTM ()
otDecl (HDSort s) = pushSort s >> emit ["pop"]
otDecl (HDTerm x (HType ss t)) = do
  n <- app "constTerm" [
    app "const" [str x],
    arrows (pushSType <$> ss) (pushSType t)] >> save
  modify $ \g -> g {otTerms = M.insert x n (otTerms g)}
otDecl (HDDef x ss xs r t) = do
  str x
  let ss' = ss ++ ((\(x, s) -> (x, SType [] s)) <$> xs)
  push <- otDef ss' t
  emit ["defineConst"]
  n <- push >> save
  arrows (pushSType . snd <$> ss) (pushSType (SType (snd <$> xs) r))
  c <- emit ["constTerm"] >> save
  modify $ \g -> g {
    otTerms = M.insert x c (otTerms g),
    otDefs = M.insert x (ss, xs, t, n) (otDefs g) }
otDecl (HDThm x ty@(TType vs gs (GType xs r)) pr) = do
  ns <- mapM (\(v, t) -> (,) v <$> peekVar v t)
    (vs ++ ((\(v, t) -> (v, SType [] t)) <$> xs))
  n <- otThm x (ref' <$> M.fromList ns) gs (M.fromList xs) r pr
  modify $ \g -> g {
    otThms = M.insert x (ty, n, ns) (otThms g),
    otHyps = mempty,
    otHypApps = mempty }

otDef :: [(Ident, SType)] -> Term -> OTM (OTM ())
otDef ss t = go M.empty ss where
  go :: M.Map Ident (OTM Int) -> [(Ident, SType)] -> OTM (OTM ())
  go m [] = do
    pushTerm m t
    return (return ())
  go m ((x, s) : ss) = do
    xn <- pushVar x s
    push <- go (M.insert x (ref' xn) m) ss
    n <- emit ["absTerm"] >> def
    return $ do
      app "refl" [app "varTerm" [ref xn]] >> emit ["appThm"]
      app "betaConv" [app "appTerm" [ref n, app "varTerm" [ref xn]]] >> emit ["trans"]
      push

pushGType :: M.Map Ident (OTM Int) -> GType -> OTM [Int]
pushGType m (GType xs t) = go m xs where
  go :: M.Map Ident (OTM Int) -> [(Ident, Sort)] -> OTM [Int]
  go m [] = pushTerm m t >> return []
  go m ((x, s) : ss) = do
    pushAllC s
    n <- pushVar x (SType [] s)
    ls <- go (M.insert x (ref' n) m) ss
    l <- emit ["absTerm"] >> def
    emit ["appTerm"] >> return (l : ls)

type OTCtx = (M.Map Ident Sort, M.Map Ident (OTM Int))

pushHyp :: OTCtx -> Ident -> [Ident] -> OTM (Term, Int)
pushHyp (xm, _) h xs = do
  g <- get
  case otHypApps g M.!? (h, xs) of
    Just (ty, n) -> (,) ty <$> ref' n
    Nothing -> do
      let (GType ts ty, ls, nh) = otHyps g <!> h
      n <- go xs ls nh >> def
      let r = (vsubstTerm (M.fromList (zip (fst <$> ts) xs)) ty, n)
      modify $ \g -> g {otHypApps = M.insert (h, xs) r (otHypApps g)}
      return r
  where
  go :: [Ident] -> [Int] -> Int -> OTM ()
  go [] [] n = ref n
  go (x:xs) (l:ls) n = do
    let s = xm <!> x
    forallElim s (go xs ls n) (ref l) $
      app "varTerm" [pushVar x (SType [] s)]

otThm :: Ident -> M.Map Ident (OTM Int) -> [GType] ->
  M.Map Ident Sort -> Term -> Maybe ([Ident], HProof) -> OTM Int
otThm name m gs vm ret pf = do
  (hns, hts) <- fmap unzip $ forM gs $ \h -> do
    ty <- pushGType m h
    n <- def
    n' <- emit ["assume"] >> save
    return ((h, ty, n'), n)
  case pf of
    Just (hs, p) -> do
      str name
      modify $ \g -> g {otHyps = M.fromList (zip hs hns)}
      n <- pushProof (vm, m) p >> def
      list (ref <$> hts) >> pushTerm m ret
      emit ["thm"] >> return n
    Nothing -> do
      str name
      list (ref <$> hts) >> pushTerm m ret
      emit ["axiom"] >> save

pushProof :: OTCtx -> HProof -> OTM Term
pushProof ctx (HHyp h xs) = fst <$> pushHyp ctx h xs
pushProof ctx@(_, m) (HThm t es ps ys) = do
  g <- get
  let (TType ts hs (GType ss r), nt, nvs) = otThms g <!> t
  ns <- forM ps $ \p -> pushProofLam ctx p >> save
  foldl (\push n -> app "proveHyp" [ref n, push])
    (app "subst" [list [list [], list $
      zipWith (\(x, n) e -> list [ref n, pushSLam m e]) nvs
        (es ++ (SLam [] . LVar <$> ys))],
      ref nt]) ns
  let vm = M.fromList (zip (fst <$> ts) es)
  let (ss', r') = substAbs vm ss r
  return $ vsubstTerm (M.fromList (zip (fst <$> ss') ys)) r'
pushProof ctx (HSave h pl@(HProofLam ss p) ys) = do
  (ret@(GType ss r), d, ls) <- pushProofLam ctx pl
  n <- def
  modify $ \g -> g {
    otHyps = M.insert h (ret, ls, n) (otHyps g),
    otHypApps = M.insert (h, ys) (r, d) (otHypApps g) }
  return r
pushProof ctx (HForget (HProofLam ss p)) =
  pushProof (foldl (\(xm, m) (x, s) ->
    (M.insert x s xm, M.insert x (pushVar x (SType [] s)) m)) ctx ss) p
pushProof ctx (HConv eq p) = do
  (_, t2) <- pushConv ctx eq
  n <- save
  app "eqMp" [() <$ pushProof ctx p, ref n]
  return t2
pushProof ctx HSorry = error "sorry found"

pushProofLam :: OTCtx -> HProofLam -> OTM (GType, Int, [Int])
pushProofLam ctx (HProofLam xs p) = do
  (t, d, ls, _) <- go ctx xs
  return (GType xs t, d, ls)
  where
  go :: OTCtx -> [(Ident, Sort)] -> OTM (Term, Int, [Int], OTM ())
  go ctx@(_, m) [] = do
    (t, d) <- liftM2 (,) (pushProof ctx p) def
    return (t, d, [], pushTerm m t)
  go (xm, m) ((x, s) : xs) = do
    let pushX = pushVar x (SType [] s)
    (t, d, ls, pushT) <- go (M.insert x s xm, M.insert x pushX m) xs
    pr <- save
    (l, pushT') <- forallIntro s (() <$ pushX) pushT (ref pr)
    return (t, d, l : ls, pushT')

pushConv :: OTCtx -> HConv -> OTM (Term, Term)
pushConv ctx@(_, m) (CRefl e) = do
  app "refl" [pushTerm m e]
  return (e, e)
pushConv ctx (CSymm p) = do
  (e1, e2) <- pushConv ctx p
  emit ["sym"] >> return (e2, e1)
pushConv ctx (CTrans p1 p2) = do
  (e1, _) <- pushConv ctx p1
  (_, e2) <- pushConv ctx p1
  emit ["trans"] >> return (e1, e2)
pushConv ctx@(_, m) (CCong t ps xs) = do
  app "refl" [get >>= ref . (<!> t) . otTerms]
  (es, es') <- fmap unzip $ forM ps $ \p -> pushConvLam ctx p <* emit ["appThm"]
  forM_ xs $ \x -> app "refl" [pushTerm m (LVar x)] >> emit ["appThm"]
  return (HApp t es xs, HApp t es' xs)
pushConv ctx@(_, m) (CDef t es xs) = do
  (ts, ss, e, n) <- (<!> t) . otDefs <$> get
  app "subst" [
    list [list [], list $
      zipWith (\(x, s) e -> list
        [() <$ pushVar x s, pushSLam m e]) ts es ++
      zipWith (\(x, s) e -> list
        [() <$ pushVar x (SType [] s), pushTerm m (LVar e)]) ss xs],
    ref n]
  let (ss', l) = substAbs (M.fromList (zip (fst <$> ts) es)) ss e
      e' = vsubstTerm (M.fromList (zip (fst <$> ss') xs)) l
  return (HApp t es xs, e')

pushConvLam :: OTCtx -> HConvLam -> OTM (SLam, SLam)
pushConvLam ctx (HConvLam ss p) = do
  (e1, e2) <- go ctx ss
  return (SLam ss e1, SLam ss e2)
  where
  go :: OTCtx -> [(Ident, Sort)] -> OTM (Term, Term)
  go ctx [] = pushConv ctx p
  go (xm, m) ((x, s) : xs) = do
    n <- pushVar x (SType [] s)
    go (M.insert x s xm, M.insert x (ref' n) m) xs <* emit ["absThm"]
