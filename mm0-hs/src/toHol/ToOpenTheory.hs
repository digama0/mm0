module ToOpenTheory where

import Data.Semigroup
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State.Strict
import qualified Data.Map.Strict as M
import Environment (Ident)
import HolTypes

data OTState = OTState {
  otDict :: Int,
  otArrow :: Maybe Int,
  otAll :: (Int, Int, Int, Int),
  otAllConst :: M.Map Sort Int,
  otSorts :: M.Map Ident Int,
  otProv :: M.Map Ident Int,
  otEqs :: M.Map [Sort] Int,
  otTerms :: M.Map Ident (Int, Sort),
  otDefs :: M.Map Ident ([(Ident, SType)], [(Ident, Sort)], Term, Int),
  otTypes :: M.Map SType Int,
  otVars :: M.Map (Ident, SType) Int,
  otThms :: M.Map Ident (TType, Int, [(Ident, Int)]),
  otHyps :: M.Map Ident (GType, [Int], Int),
  otHypApps :: M.Map (Ident, [Ident]) (Term, Int)
}

mkOTState :: OTState
mkOTState = OTState 0 Nothing undefined mempty mempty mempty
  mempty mempty mempty mempty mempty mempty mempty mempty

type OTM m = ReaderT (String -> m ()) (StateT OTState m)

writeOT :: Monad m => (String -> m ()) -> [HDecl] -> m ()
writeOT f ds = evalStateT (runReaderT (preamble >> mapM_ otDecl ds) f) mkOTState

otToString :: [HDecl] -> [String]
otToString ds = appEndo (execWriter $ writeOT (tell . Endo . (:)) ds) []

emit :: Monad m => [String] -> OTM m ()
emit = mapM_ $ \s -> do f <- ask; lift $ lift $ f s

ref :: Monad m => Int -> OTM m ()
ref n = app "ref" [emit [show n]]

ref' :: Monad m => Int -> OTM m Int
ref' n = ref n >> return n

def :: Monad m => OTM m Int
def = do
  g <- get
  let n = otDict g
  app "def" [emit [show n]]
  put $ g {otDict = n + 1}
  return n

save :: Monad m => OTM m Int
save = def <* emit ["pop"]

pushWith :: Monad m => (OTState -> Maybe Int) -> (Int -> OTState -> OTState) -> OTM m () -> OTM m Int
pushWith r w go = do
  g <- get
  case r g of
    Just n -> ref' n
    Nothing -> do n <- go >> def; modify (w n); return n

pushSort :: Monad m => Sort -> OTM m Int
pushSort x = pushWith (\g -> otSorts g M.!? x)
  (\n g -> g {otSorts = M.insert x n (otSorts g)}) $
  app "opType" [app "typeOp" [str x], list []]

pushProv :: Monad m => Sort -> OTM m Int
pushProv x = pushWith (\g -> otProv g M.!? x)
  (\n g -> g {otProv = M.insert x n (otProv g)}) $
  app "constTerm" [
    app "const" [str (x ++ ".|-")],
    () <$ pushSType (SType [x] "bool")]

app :: Monad m => String -> [OTM m a] -> OTM m ()
app s [] = emit [s]
app s (m:ms) = m >> app s ms

str :: Monad m => String -> OTM m ()
str s = emit [show s]

list :: Monad m => [OTM m a] -> OTM m ()
list [] = emit ["nil"]
list (m:ms) = m >> list ms >> emit ["cons"]

bool :: Monad m => OTM m Int
bool = pushSType (SType [] "bool")

preamble :: Monad m => OTM m ()
preamble = do
  app "version" [emit ["6"]]
  -- (
  str "OT.T" -- name OT.T
  let bb = pushSType (SType ["bool"] "bool")
  --   ( (
  app "constTerm" [app "const" [str "="], arrows [bb, bb] bool]
    -- = : (bool -> bool) -> (bool -> bool) -> bool
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
  tru <- app "eqMp" [ref th, app "refl" [ref idb]] >> save -- |- T

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
  al <- save -- const !
  alth <- app "eqMp" [
    app "sym" [app "trans" [
      app "appThm" [
        app "eqMp" [ref ap,
          app "assume" [
            app "appTerm" [
              app "constTerm" [ref al, arrows [ref ab] bool],
              ref pt]] -- {! P} |- ! P
          ], -- {! P} |- P = \a. T
        app "refl" [app "varTerm" [ref a]]], -- {! P} |- P a = (\a. T) a
      app "betaConv" [
        app "appTerm" [ref lamt, app "varTerm" [ref a]]] -- |- (\a. T) a = T
      ]], -- {! P} |- T = P a
    ref tru] >> save -- {! P} |- P a
  apr <- app "sym" [ref ap] >> save -- |- (P = \a. T) = ! P
  modify $ \g -> g {otAll = (al, tru, apr, alth)}

pushArrow :: Monad m => OTM m Int
pushArrow = pushWith otArrow (\n g -> g {otArrow = Just n}) $ do
  app "typeOp" [str "->"]

arrows :: Monad m => [OTM m a] -> OTM m b -> OTM m ()
arrows [] r = () <$ r
arrows (m : ms) r = app "opType" [
  () <$ pushArrow, list [() <$ m, () <$ arrows ms r]]

pushSType :: Monad m => SType -> OTM m Int
pushSType s@(SType ss t) = pushWith (\g -> otTypes g M.!? s)
  (\n g -> g {otTypes = M.insert s n (otTypes g)})
  (arrows (pushSort <$> ss) (pushSort t))

pushVar :: Monad m => Ident -> SType -> OTM m Int
pushVar x t = pushWith (\g -> otVars g M.!? (x, t))
  (\n g -> g {otVars = M.insert (x, t) n (otVars g)}) $ do
  app "var" [str x, () <$ pushSType t]

peekVar :: Monad m => Ident -> SType -> OTM m Int
peekVar x t = do
  g <- get
  case otVars g M.!? (x, t) of
    Just n -> return n
    Nothing -> pushVar x t <* emit ["pop"]

pushEq :: Monad m => [Sort] -> OTM m Int
pushEq ss = pushWith (\g -> otEqs g M.!? ss)
  (\n g -> g {otEqs = M.insert ss n (otEqs g)}) $
    let s = pushSType (SType ss "bool") in
    app "constTerm" [app "const" [str "="], arrows [s, s] bool]

pushAllC :: Monad m => Sort -> OTM m Int
pushAllC s = pushWith (\g -> otAllConst g M.!? s)
  (\n g -> g {otAllConst = M.insert s n (otAllConst g)}) $
    app "constTerm" [
      do (n, _, _, _) <- otAll <$> get; ref n,
      arrows [pushSType (SType [s] "bool")] bool]

-- pr: G |- ! (\x:s. t[x]), P := (\x:s. t[x]), a := a
-- pushes G |- t[a]
forallElim :: Monad m => Sort -> OTM m () -> OTM m () -> OTM m () -> OTM m ()
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
forallIntro :: Monad m => Sort -> OTM m () -> OTM m () -> OTM m () -> OTM m (Int, OTM m ())
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

type OTCtx m = (M.Map Ident Sort, M.Map Ident (OTM m Int))

otcInsert :: Monad m => Ident -> Sort -> OTCtx m -> OTCtx m
otcInsert x s (xm, m) = (M.insert x s xm, M.insert x (pushVar x (SType [] s)) m)

otcInsert' :: Monad m => Ident -> Sort -> Int -> OTCtx m -> OTCtx m
otcInsert' x s n (xm, m) = (M.insert x s xm, M.insert x (ref' n) m)

pushAppVars :: Monad m => OTCtx m -> OTM m () -> [Ident] -> OTM m ()
pushAppVars m f [] = f
pushAppVars m f (x:xs) =
  pushAppVars m (app "appTerm" [f, app "varTerm" [snd m M.! x]]) xs

pushAppLams :: Monad m => OTCtx m -> OTM m () -> [SLam] -> OTM m ()
pushAppLams m f [] = f
pushAppLams m f (l:ls) =
  pushAppLams m (app "appTerm" [f, pushSLam m l]) ls

pushSLam :: Monad m => OTCtx m -> SLam -> OTM m ()
pushSLam m (SLam ss t) = go m ss where
  go :: Monad m => OTCtx m -> [(Ident, Sort)] -> OTM m ()
  go m [] = () <$ pushTerm m t
  go m ((x, s) : ss) = do
    n <- pushVar x (SType [] s)
    go (otcInsert' x s n m) ss
    emit ["absTerm"]

pushTerm :: Monad m => OTCtx m -> Term -> OTM m Sort
pushTerm (xm, m) (LVar x) = app "varTerm" [m M.! x] >> return (xm M.! x)
pushTerm ctx@(xm, m) (RVar v xs) =
  pushAppVars ctx (app "varTerm" [m M.! v]) xs >> return (xm M.! v)
pushTerm ctx (HApp t ls xs) = do
  (n, s) <- (M.! t) . otTerms <$> get
  pushAppVars ctx (pushAppLams ctx (ref n) ls) xs
  return s

otDecl :: Monad m => HDecl -> OTM m ()
otDecl (HDSort s) = pushSort s >> emit ["pop"]
otDecl (HDTerm x (HType ss t@(SType _ s))) = do
  n <- app "constTerm" [
    app "const" [str x],
    arrows (pushSType <$> ss) (pushSType t)] >> save
  modify $ \g -> g {otTerms = M.insert x (n, s) (otTerms g)}
otDecl (HDDef x ss xs r t) = do
  str x
  let ss' = ss ++ ((\(x, s) -> (x, SType [] s)) <$> xs)
  push <- otDef ss' t
  emit ["defineConst"]
  n <- push >> save
  arrows (pushSType . snd <$> ss) (pushSType (SType (snd <$> xs) r))
  c <- emit ["constTerm"] >> save
  modify $ \g -> g {
    otTerms = M.insert x (c, r) (otTerms g),
    otDefs = M.insert x (ss, xs, t, n) (otDefs g) }
otDecl (HDThm x ty@(TType vs gs (GType xs r)) pr) = do
  ns <- mapM (\(v, t) -> (,) v <$> peekVar v t)
    (vs ++ ((\(v, t) -> (v, SType [] t)) <$> xs))
  n <- otThm (
    M.fromList (((\(v, SType _ s) -> (v, s)) <$> vs) ++ xs),
    ref' <$> M.fromList ns) gs r pr
  modify $ \g -> g {
    otThms = M.insert x (ty, n, ns) (otThms g),
    otHyps = mempty,
    otHypApps = mempty }

otDef :: Monad m => [(Ident, SType)] -> Term -> OTM m (OTM m ())
otDef ss t = go mempty ss where
  go :: Monad m => OTCtx m -> [(Ident, SType)] -> OTM m (OTM m ())
  go m [] = do
    pushTerm m t
    return (return ())
  go m ((x, s@(SType _ so)) : ss) = do
    xn <- pushVar x s
    push <- go (otcInsert' x so xn m) ss
    n <- emit ["absTerm"] >> def
    return $ do
      app "refl" [app "varTerm" [ref xn]] >> emit ["appThm"]
      app "betaConv" [app "appTerm" [ref n, app "varTerm" [ref xn]]] >> emit ["trans"]
      push

pushGType :: Monad m => OTCtx m -> GType -> OTM m [Int]
pushGType ctx (GType xs t) = go ctx xs where
  go :: Monad m => OTCtx m -> [(Ident, Sort)] -> OTM m [Int]
  go ctx [] = do
    s <- pushTerm ctx t
    n <- save
    app "appTerm" [pushProv s, ref' n] >> return []
  go ctx ((x, s) : ss) = do
    pushAllC s
    n <- pushVar x (SType [] s)
    ls <- go (otcInsert' x s n ctx) ss
    l <- emit ["absTerm"] >> def
    emit ["appTerm"] >> return (l : ls)

pushHyp :: Monad m => OTCtx m -> Ident -> [Ident] -> OTM m (Term, Int)
pushHyp (xm, _) h xs = do
  g <- get
  case otHypApps g M.!? (h, xs) of
    Just (ty, n) -> (,) ty <$> ref' n
    Nothing -> do
      let (GType ts ty, ls, nh) = otHyps g M.! h
      n <- go xs ls nh >> def
      let r = (vsubstTerm (M.fromList (zip (fst <$> ts) xs)) ty, n)
      modify $ \g -> g {otHypApps = M.insert (h, xs) r (otHypApps g)}
      return r
  where
  go :: Monad m => [Ident] -> [Int] -> Int -> OTM m ()
  go [] [] n = ref n
  go (x:xs) (l:ls) n = do
    let s = xm M.! x
    forallElim s (go xs ls n) (ref l) $
      app "varTerm" [pushVar x (SType [] s)]

otThm :: Monad m => OTCtx m -> [GType] ->
  Term -> Maybe ([Ident], HProof) -> OTM m Int
otThm ctx gs ret pf = do
  (hns, hts) <- fmap unzip $ forM gs $ \h -> do
    ty <- pushGType ctx h
    n <- def
    n' <- emit ["assume"] >> save
    return ((h, ty, n'), n)
  case pf of
    Just (hs, p) -> do
      modify $ \g -> g {otHyps = M.fromList (zip hs hns)}
      n <- pushProof ctx p >> def
      list (ref <$> hts) >> pushGType ctx (GType [] ret)
      emit ["thm"] >> return n
    Nothing -> do
      list (ref <$> hts) >> pushGType ctx (GType [] ret)
      emit ["axiom"] >> save

pushProof :: Monad m => OTCtx m -> HProof -> OTM m Term
pushProof ctx (HHyp h xs) = fst <$> pushHyp ctx h xs
pushProof ctx (HThm t es ps ys) = do
  g <- get
  let (TType ts hs (GType ss r), nt, nvs) = otThms g M.! t
  ns <- forM ps $ \p -> pushProofLam ctx p >> save
  foldl (\push n -> app "proveHyp" [ref n, push])
    (app "subst" [list [list [], list $
      zipWith (\(x, n) e -> list [ref n, pushSLam ctx e]) nvs
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

pushProofLam :: Monad m => OTCtx m -> HProofLam -> OTM m (GType, Int, [Int])
pushProofLam ctx (HProofLam xs p) = do
  (t, d, ls, _) <- go ctx xs
  return (GType xs t, d, ls)
  where
  go :: Monad m => OTCtx m -> [(Ident, Sort)] -> OTM m (Term, Int, [Int], OTM m ())
  go ctx [] = do
    (t, d) <- liftM2 (,) (pushProof ctx p) def
    return (t, d, [], () <$ pushTerm ctx t)
  go ctx ((x, s) : xs) = do
    (t, d, ls, pushT) <- go (otcInsert x s ctx) xs
    pr <- save
    (l, pushT') <- forallIntro s (() <$ pushVar x (SType [] s)) pushT (ref pr)
    return (t, d, l : ls, pushT')

pushConv :: Monad m => OTCtx m -> HConv -> OTM m (Term, Term)
pushConv ctx (CRefl e) = do
  app "refl" [pushTerm ctx e]
  return (e, e)
pushConv ctx (CSymm p) = do
  (e1, e2) <- pushConv ctx p
  emit ["sym"] >> return (e2, e1)
pushConv ctx (CTrans p1 p2) = do
  (e1, _) <- pushConv ctx p1
  (_, e2) <- pushConv ctx p1
  emit ["trans"] >> return (e1, e2)
pushConv ctx (CCong t ps xs) = do
  app "refl" [get >>= ref . fst . (M.! t) . otTerms]
  (es, es') <- fmap unzip $ forM ps $ \p -> pushConvLam ctx p <* emit ["appThm"]
  forM_ xs $ \x -> app "refl" [pushTerm ctx (LVar x)] >> emit ["appThm"]
  return (HApp t es xs, HApp t es' xs)
pushConv ctx (CDef t es xs) = do
  (ts, ss, e, n) <- (M.! t) . otDefs <$> get
  app "subst" [
    list [list [], list $
      zipWith (\(x, s) e -> list
        [() <$ pushVar x s, () <$ pushSLam ctx e]) ts es ++
      zipWith (\(x, s) e -> list
        [() <$ pushVar x (SType [] s), () <$ pushTerm ctx (LVar e)]) ss xs],
    ref n]
  let (ss', l) = substAbs (M.fromList (zip (fst <$> ts) es)) ss e
      e' = vsubstTerm (M.fromList (zip (fst <$> ss') xs)) l
  return (HApp t es xs, e')

pushConvLam :: Monad m => OTCtx m -> HConvLam -> OTM m (SLam, SLam)
pushConvLam ctx (HConvLam ss p) = do
  (e1, e2) <- go ctx ss
  return (SLam ss e1, SLam ss e2)
  where
  go :: Monad m => OTCtx m -> [(Ident, Sort)] -> OTM m (Term, Term)
  go ctx [] = pushConv ctx p
  go (xm, m) ((x, s) : xs) = do
    n <- pushVar x (SType [] s)
    go (M.insert x s xm, M.insert x (ref' n) m) xs <* emit ["absThm"]
