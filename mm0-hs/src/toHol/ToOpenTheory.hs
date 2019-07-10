{-# LANGUAGE ScopedTypeVariables #-}
module ToOpenTheory(writeOT, otToString) where

import Prelude hiding (log)
import Data.Default
import Data.Semigroup
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State.Strict
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import HolTypes
import Util

data OTPreamble = OTPreamble {
  otpTrue :: Int,  -- |- T
  otpAll :: Int,   -- const !
  otpAllI :: Int,  -- |- (P = \a. T) = ! P
  otpAllE :: Int } -- {! P} |- P a

data OTState = OTState {
  otDict :: Int,
  otArrow :: Maybe Int,
  otPreamble :: OTPreamble,
  otAllConst :: M.Map Sort Int,
  otSorts :: M.Map Ident Int,
  otProv :: M.Map Ident Int,
  otEqs :: M.Map [Sort] Int,
  otTerms :: M.Map Ident (Int, Sort),
  otDefs :: M.Map Ident ([(Ident, SType)], [(Ident, Sort)], Term, Int),
  otTypes :: M.Map SType Int,
  otVars :: M.Map (Ident, SType) Int,
  otThms :: M.Map Ident (TType, Sort, Int),
  otHyps :: M.Map Ident (GType, Sort, [Int], Int),
  otHypApps :: M.Map (Ident, [Ident]) (Term, Sort, Int)
}

instance Default OTState where
  def = OTState def def undefined def def def def def def def def def def def

type OTM m = ReaderT (String -> m ()) (StateT OTState m)

writeOT :: Monad m => (String -> m ()) -> [HDecl] -> m ()
writeOT f ds = evalStateT (runReaderT (preamble >> mapM_ otDecl ds >>
  get >>= cleanup . otDict) f) def where
  cleanup :: Monad m => Int -> OTM m ()
  cleanup 0 = return ()
  cleanup n = app "pop" [app "remove" [emit [show (n-1)]]] >> cleanup (n-1)

otToString :: [HDecl] -> [String]
otToString ds = appEndo (execWriter $ writeOT (tell . Endo . (:)) ds) []

emit :: Monad m => [String] -> OTM m ()
emit = mapM_ $ \s -> do f <- ask; lift $ lift $ f s

ref :: Monad m => Int -> OTM m ()
ref n = app "ref" [emit [show n]]

ref' :: Monad m => Int -> OTM m Int
ref' n = ref n >> return n

def' :: Monad m => OTM m Int
def' = do
  g <- get
  let n = otDict g
  app "def" [emit [show n]]
  put $ g {otDict = n + 1}
  return n

save :: Monad m => OTM m Int
save = def' <* emit ["pop"]

log :: Monad m => String -> OTM m ()
log s = emit ["# " ++ s]

debug :: Monad m => String -> OTM m ()
debug s = app "pragma" [str "debug"] >> log s

pushWith :: Monad m => (OTState -> Maybe Int) -> (Int -> OTState -> OTState) -> OTM m () -> OTM m Int
pushWith r w go = do
  g <- get
  case r g of
    Just n -> ref' n
    Nothing -> do n <- go >> def'; modify (w n); return n

pushSort :: Monad m => Sort -> OTM m Int
pushSort x = pushWith (\g -> otSorts g M.!? x)
  (\n g -> g {otSorts = M.insert x n (otSorts g)}) $
  app "opType" [app "typeOp" [str x], list []]

pushProv :: Monad m => Sort -> OTM m Int
pushProv x = pushWith (\g -> otProv g M.!? x)
  (\n g -> g {otProv = M.insert x n (otProv g)}) $
  app "constTerm" [
    app "const" [str (x <> ".|-")],
    () <$ pushSType (SType [x] "bool")]

app :: Monad m => String -> [OTM m a] -> OTM m ()
app s [] = emit [s]
app s (m:ms) = m >> app s ms

str :: Monad m => T.Text -> OTM m ()
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
  str "Data.Bool.T" -- name T
  let bb = pushSType (SType ["bool"] "bool")
  --   ( (
  app "constTerm" [app "const" [str "="], arrows [bb, bb] bool]
    -- = : (bool -> bool) -> (bool -> bool) -> bool
  idb <- pushVar "x" (SType [] "bool") >>
    def' >>= ref >> emit ["varTerm", "absTerm"] >> def'
    -- term \(x : bool), (x : bool)
  emit ["appTerm"]
  --     )
  ref idb
  e <- emit ["appTerm"] >> def' -- term (\(x : bool), x) = (\(x : bool), x)
  --   )
  th <- emit ["defineConst", "sym"] >> save -- |- ((\x. x) = (\x. x)) = T
  ctru <- bool >> emit ["constTerm"] >> save -- T : bool
  -- )
  tru <- app "eqMp" [ref th, app "refl" [ref idb]] >> save -- |- T

  -- (
  str "Data.Bool.!" -- name !
  --   (
  str "p"
  ab <- arrows [app "varType" [str "A"]] bool >> def' -- type A -> bool
  p <- emit ["var"] >> def' -- p : A -> bool
  --   )
  --   ( ( (
  app "constTerm" [app "const" [str "="],
    arrows [ref ab, ref ab] bool] -- = : (A -> bool) -> (A -> bool) -> bool
  pt <- app "varTerm" [ref p] >> def'
  emit ["appTerm"] -- (=) p
  --       )
  --       (
  a <- app "var" [str "a", app "varType" [str "A"]] >> def' -- a : A
  ref ctru
  lamt <- emit ["absTerm"] >> def' -- \(a : A). T
  --       )
  emit ["appTerm"]
  --     )
  lam <- emit ["absTerm"] >> def' -- \(P : A -> bool). (P = \(a : A). T)
  --   )
  emit ["defineConst"] -- |- ! = \(P : A -> bool). (P = \(a : A). T)
  -- )
  ap <- app "refl" [ref pt] >> emit ["appThm"] >> -- |- ! P = (\P. (P = \a. T)) P
    app "betaConv" [app "appTerm" [ref lam, ref pt]] >> emit ["trans"] >> save -- |- ! P = (P = \a. T)
  al <- save -- const !
  ale <- app "eqMp" [
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
  ali <- app "sym" [ref ap] >> save -- |- (P = \a. T) = ! P
  modify $ \g -> g {otPreamble = OTPreamble tru al ali ale}

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
      get >>= ref .  otpAll . otPreamble,
      arrows [pushSType (SType [s] "bool")] bool]

-- pr: G |- ! (\x:s. t[x]), P := (\x:s. t[x]), a := a
-- pushes G |- t[a]
forallElim :: Monad m => Sort -> OTM m () -> OTM m () -> OTM m () -> OTM m ()
forallElim s pr p a = do
  otp <- gets otPreamble
  app "proveHyp" [ -- G |- t[a]
    pr, -- G |- ! (\x:s. t[x])
    app "eqMp" [ -- {! P} |- t[a]
      app "betaConv" [app "appTerm" [p, a]],
      app "subst" [ -- {! P} |- (\x:s. t[x]) a
        list [list [list [emit [show "A"], () <$ pushSType (SType [] s)]],
              list [list [() <$ pushVar "p" (SType [s] "bool"), p],
                    list [() <$ pushVar "a" (SType [] s), a]]],
        ref (otpAllE otp)]]]

-- var x : s, term t, pr: G |- t[x]
-- pushes G |- ! (\x:s, t[x]), returns term (\x:s, t[x]), term ! (\x:s, t[x])
forallIntro :: Monad m => Sort -> OTM m () -> OTM m () -> OTM m () -> OTM m (Int, OTM m ())
forallIntro s x t pr = do
  otp <- gets otPreamble
  l <- app "absTerm" [x, t] >> save
  app "eqMp" [ -- G |- ! (\x:s. t[x])
    app "subst" [ -- |- ((\x:s. t[x]) = (\x:s. T)) = ! (\x:s. t[x])
      list [
        list [list [emit [show "A"], () <$ pushSType (SType [] s)]],
        list [list [pushVar "p" (SType [s] "bool"), ref' l]]],
      ref (otpAllI otp)],
    app "absThm" [x, app "deductAntisym" [pr, ref (otpTrue otp)]]]
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
  (n, s) <- gets ((M.! t) . otTerms)
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
  let ss' = ss ++ (mapSnd (SType []) <$> xs)
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
    (vs ++ (mapSnd (SType []) <$> xs))
  (n, so) <- otThm (
    M.fromList ((mapSnd (\(SType _ s) -> s) <$> vs) ++ xs),
    ref' <$> M.fromList ns) gs r pr
  modify $ \g -> g {
    otThms = M.insert x (ty, so, n) (otThms g),
    otHyps = mempty,
    otHypApps = mempty }
  emit ["# theorem " ++ T.unpack x]

otDef :: Monad m => [(Ident, SType)] -> Term -> OTM m (OTM m ())
otDef ss t = go mempty ss where
  go :: Monad m => OTCtx m -> [(Ident, SType)] -> OTM m (OTM m ())
  go m [] = do
    pushTerm m t
    return (return ())
  go m ((x, s@(SType _ so)) : ss) = do
    xn <- pushVar x s
    push <- go (otcInsert' x so xn m) ss
    n <- emit ["absTerm"] >> def'
    return $ do
      app "refl" [app "varTerm" [ref xn]] >> emit ["appThm"]
      app "betaConv" [app "appTerm" [ref n, app "varTerm" [ref xn]]] >> emit ["trans"]
      push

pushGType :: Monad m => OTCtx m -> GType -> OTM m ([Int], Sort)
pushGType ctx (GType xs t) = go ctx xs where
  go :: Monad m => OTCtx m -> [(Ident, Sort)] -> OTM m ([Int], Sort)
  go ctx [] = do
    s <- pushTerm ctx t
    n <- save
    app "appTerm" [pushProv s, ref' n] >> return ([], s)
  go ctx ((x, s) : ss) = do
    pushAllC s
    n <- pushVar x (SType [] s)
    (ls, so) <- go (otcInsert' x s n ctx) ss
    l <- emit ["absTerm"] >> def'
    emit ["appTerm"] >> return (l : ls, so)

pushHyp :: Monad m => OTCtx m -> Ident -> [Ident] -> OTM m (Term, Sort, Int)
pushHyp (xm, _) h xs = do
  g <- get
  case otHypApps g M.!? (h, xs) of
    Just (ty, so, n) -> (,,) ty so <$> ref' n
    Nothing -> do
      let (GType ts ty, so, ls, nh) = otHyps g M.! h
      n <- go xs ls (ref nh) >> def'
      let r = (vsubstTerm (M.fromList (zip (fst <$> ts) xs)) ty, so, n)
      modify $ \g -> g {otHypApps = M.insert (h, xs) r (otHypApps g)}
      return r
  where
  go :: Monad m => [Ident] -> [Int] -> OTM m () -> OTM m ()
  go [] [] pr = pr
  go (x:xs) (l:ls) pr = go xs ls $ let s = xm M.! x in
    forallElim s pr (ref l) $ app "varTerm" [pushVar x (SType [] s)]

data OTConv m = OTCRefl (OTM m ()) | OTCEq (OTM m ())

otcToEq :: Monad m => OTConv m -> OTM m ()
otcToEq (OTCRefl t) = app "refl" [t]
otcToEq (OTCEq e) = e

otcToMaybe :: Monad m => OTConv m -> Maybe (OTM m ())
otcToMaybe (OTCRefl _) = Nothing
otcToMaybe (OTCEq e) = Just e

otcIsRefl :: OTConv m -> Bool
otcIsRefl (OTCRefl _) = True
otcIsRefl _ = False

makeSubstList :: forall m. Monad m => OTCtx m -> [((Ident, SType), SLam)] ->
  [((Ident, Sort), Ident)] -> OTM m ()
makeSubstList ctx es xs = list [list [], list $
  ((\((x, s), e) -> list [
    () <$ pushVar x s, () <$ pushSLam ctx e]) <$> es) ++
  ((\((x, s), e) -> list [
    () <$ pushVar x (SType [] s), () <$ pushTerm ctx (LVar e)]) <$> xs)]

makeSubst :: forall m. Monad m => OTState -> OTCtx m -> [((Ident, SType), SLam)] ->
  [((Ident, Sort), Ident)] -> Term -> (Term, Maybe (OTM m ()))
makeSubst g ctx es xs t = go ctx M.empty xs where
  go :: OTCtx m -> M.Map Ident (Sort, Ident) ->
    [((Ident, Sort), Ident)] -> (Term, Maybe (OTM m ()))
  go ctx vm [] = let (t', _, p) = makeSubstTerm g ctx vm es t in (t', p)
  go ctx vm (((v, s), y) : vs) = go (otcInsert y s ctx) (M.insert v (s, y) vm) vs

makeSubstGType :: Monad m => OTState -> OTCtx m -> [((Ident, SType), SLam)] ->
    GType -> (GType, Maybe (OTM m ()))
makeSubstGType g ctx es (GType vs t) = go ctx M.empty vs where
  em :: M.Map Ident (SLam, Sort)
  em = M.fromList ((\((x, SType _ s), e) -> (x, (e, s))) <$> es)
  free :: S.Set Ident
  free = foldMap (fvLam . fst . (em M.!)) (fvRTerm t)
  go ctx vm [] =
    let (t', so, pr) = makeSubstTerm g ctx vm es t in
    (GType [] t', (\p -> app "appThm" [app "refl" [pushProv so], p]) <$> pr)
  go ctx vm ((v, s) : vs) = (GType ((v', s) : ss') t', f <$> p) where
    v' = variant free v
    (GType ss' t', p) = go (otcInsert v' s ctx) (M.insert v (s, v') vm) vs
    f pushE = app "appThm" [app "refl" [pushAllC s],
      app "absThm" [() <$ pushVar v' (SType [] s), pushE]]

makeSubstTerm :: forall m. Monad m => OTState -> OTCtx m ->
  M.Map Ident (Sort, Ident) -> [((Ident, SType), SLam)] ->
  Term -> (Term, Sort, Maybe (OTM m ()))
makeSubstTerm g ctx vm es t = (t', so, otcToMaybe p) where
  (t', so, p) = makeSubstTerm' ctx vm
    (foldMap (fvLam . fst . (em M.!)) (fvRTerm t) <>
     foldMap (S.singleton . snd) vm) t
  em :: M.Map Ident (SLam, Sort)
  em = M.fromList ((\((x, SType _ s), e) -> (x, (e, s))) <$> es)

  makeSubstTerm' :: OTCtx m -> M.Map Ident (Sort, Ident) -> S.Set Ident ->
    Term -> (Term, Sort, OTConv m)
  makeSubstTerm' ctx vm free (LVar x) = let (s, y) = vm M.! x in
    (LVar y, s, OTCRefl (app "varTerm" [pushVar y (SType [] s)]))
  makeSubstTerm' ctx vm free (RVar v []) =
    let (SLam [] t, so) = em M.! v in (t, so, OTCRefl (() <$ pushTerm ctx t))
  makeSubstTerm' ctx vm free (RVar v xs) = case go ss ys of
    (pushL, pushE) -> (t', so, OTCEq $ do
      ls <- pushL
      emit ["pop"]
      pushE ls Nothing)
    where
    (SLam ss t, so) = em M.! v
    ys = snd . (vm M.!) <$> xs
    t' = vsubstTerm (M.fromList (zip (fst <$> ss) ys)) t
    go :: [(Ident, Sort)] -> [Ident] ->
      (OTM m [Int], [Int] -> Maybe (OTM m ()) -> OTM m ())
    go [] [] = (pushTerm ctx t' >> return [], \[] (Just e) -> e)
    go ((_, s) : ss) (y : ys) = (pushL', pushE') where
      (pushL, pushE) = go ss ys
      pushL' = do
        pushVar y (SType [] s)
        ls <- pushL
        l <- emit ["absTerm"] >> def'
        return (l : ls)
      pushE' (l : ls) p = pushE ls $ Just $ case p of
        Just e -> app "trans" [app "appThm" [e, app "refl" [vy]], th]
        Nothing -> th
        where
        vy = app "varTerm" [pushVar y (SType [] s)]
        th = app "betaConv" [app "appTerm" [ref l, vy]]
  makeSubstTerm' ctx vm free (HApp t es xs) =
    let (es', pushs) = unzip (makeSubstSLam ctx vm free <$> es)
        pushT = OTCRefl (get >>= ref . fst . (M.! t) . otTerms) in
    (HApp t es' ((\x -> maybe x snd (vm M.!? x)) <$> xs),
      snd (otTerms g M.! t),
      makeSubstAppLams
        (if all otcIsRefl pushs then pushT else OTCEq (otcToEq pushT)) pushs)
    where
    app1 :: OTConv m -> OTConv m -> OTConv m
    app1 (OTCRefl t) (OTCRefl x) = OTCRefl (app "appTerm" [t, x])
    app1 (OTCEq e) x = OTCEq (app "appThm" [e, otcToEq x])
    makeSubstAppLams :: OTConv m -> [OTConv m] -> OTConv m
    makeSubstAppLams p (l : ls) = makeSubstAppLams (app1 p l) ls
    makeSubstAppLams p [] = makeSubstAppVars p xs
    makeSubstAppVars :: OTConv m -> [Ident] -> OTConv m
    makeSubstAppVars p (x : xs) = makeSubstAppVars (app1 p vy) xs where
      pushY = let (s, y) = vm M.! x in pushVar y (SType [] s)
      vy = OTCRefl (app "varTerm" [pushY])
    makeSubstAppVars p [] = p

  makeSubstSLam :: OTCtx m -> M.Map Ident (Sort, Ident) -> S.Set Ident -> SLam -> (SLam, OTConv m)
  makeSubstSLam ctx vm free (SLam [] t) =
    let (t', _, p) = makeSubstTerm' ctx vm free t in (SLam [] t', p)
  makeSubstSLam ctx vm free (SLam ((v, s) : vs) t) = (SLam ((v', s) : ss') t', p') where
    v' = variant free v
    (SLam ss' t', p) = makeSubstSLam
      (otcInsert v' s ctx) (M.insert v (s, v') vm) (S.insert v' free) (SLam vs t)
    p' = case p of
      OTCRefl pushX -> OTCRefl (app "absTerm" [() <$ pushVar v' (SType [] s), pushX])
      OTCEq pushE -> OTCEq (app "absThm" [() <$ pushVar v' (SType [] s), pushE])

otThm :: Monad m => OTCtx m -> [GType] ->
  Term -> Maybe ([Ident], HProof) -> OTM m (Int, Sort)
otThm ctx gs ret pf = do
  (hns, hts) <- fmap unzip $ forM gs $ \h -> do
    (ty, so) <- pushGType ctx h
    n <- def'
    n' <- emit ["assume"] >> save
    return ((h, so, ty, n'), n)
  case pf of
    Just (hs, p) -> do
      modify $ \g -> g {otHyps = M.fromList (zip hs hns)}
      n <- pushProof ctx p >> def'
      (_, s) <- list (ref <$> hts) >> pushGType ctx (GType [] ret)
      emit ["thm"] >> return (n, s)
    Nothing -> do
      (_, s) <- list (ref <$> hts) >> pushGType ctx (GType [] ret)
      n <- emit ["axiom"] >> save
      return (n, s)

pushProof :: Monad m => OTCtx m -> HProof -> OTM m (Term, Sort)
pushProof ctx (HHyp h xs) = (\(t, so, _) -> (t, so)) <$> pushHyp ctx h xs
pushProof ctx (HThm t es ps ys) = do
  g <- get
  let (TType ts hs (GType ss r), so, nt) = otThms g M.! t
  ns <- forM ps $ \p -> liftM2 (,) (pushProofLam ctx p) save
  let es' = zip ts es
  let xs' = zip ss ys
  r' <- case makeSubst g ctx es' xs' r of
    (r', Nothing) -> r' <$ app "subst" [makeSubstList ctx es' xs', ref nt]
    (r', Just pushE) -> r' <$ app "eqMp" [
      app "appThm" [app "refl" [pushProv so], pushE],
      app "subst" [makeSubstList ctx es' xs', ref nt]]
  nth <- save
  proveHyps (snd . makeSubstGType g ctx es') hs (snd <$> ns) (ref nth)
  return (r', so)
  where
  proveHyps :: Monad m => (GType -> Maybe (OTM m ())) ->
    [GType] -> [Int] -> OTM m () -> OTM m ()
  proveHyps _ [] [] push = push
  proveHyps substG (h : hs) (n : ns) push = proveHyps substG hs ns $ do
    case substG h of
      Nothing -> app "proveHyp" [ref n, push]
      Just pushE -> app "proveHyp" [app "eqMp" [app "sym" [pushE], ref n], push]
pushProof ctx (HSave h pl@(HProofLam ss p) ys) = do
  (ret@(GType ss r), so, d, ls) <- pushProofLam ctx pl
  n <- def'
  modify $ \g -> g {
    otHyps = M.insert h (ret, so, ls, n) (otHyps g),
    otHypApps = M.insert (h, ys) (r, so, d) (otHypApps g) }
  return (r, so)
pushProof ctx (HForget _ (HProofLam ss p)) =
  pushProof (foldl (\(xm, m) (x, s) ->
    (M.insert x s xm, M.insert x (pushVar x (SType [] s)) m)) ctx ss) p
pushProof ctx (HConv eq p) = do
  (_, t2) <- pushConv ctx eq
  n <- save
  (_, so) <- pushProof ctx p
  app "appThm" [app "refl" [pushProv so], ref n] >> emit ["eqMp"]
  return (t2, so)
pushProof ctx HSorry = error "sorry found"

pushProofLam :: Monad m => OTCtx m -> HProofLam -> OTM m (GType, Sort, Int, [Int])
pushProofLam ctx (HProofLam xs p) = do
  (t, so, d, ls, _) <- go ctx xs
  return (GType xs t, so, d, ls)
  where
  go :: Monad m => OTCtx m -> [(Ident, Sort)] -> OTM m (Term, Sort, Int, [Int], OTM m ())
  go ctx [] = do
    ((t, so), d) <- liftM2 (,) (pushProof ctx p) def'
    return (t, so, d, [], app "appTerm" [() <$ pushProv so, () <$ pushTerm ctx t])
  go ctx ((x, s) : xs) = do
    (t, so, d, ls, pushT) <- go (otcInsert x s ctx) xs
    pr <- save
    (l, pushT') <- forallIntro s (() <$ pushVar x (SType [] s)) pushT (ref pr)
    return (t, so, d, l : ls, pushT')

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
  g <- get
  let (ts, ss, e, n) = otDefs g M.! t
  let es' = zip ts es
  let xs' = zip ss xs
  let (e', res) = makeSubst g ctx es' xs' e
  case res of
    Nothing -> app "subst" [makeSubstList ctx es' xs', ref n]
    Just pushE -> app "trans" [app "subst" [makeSubstList ctx es' xs', ref n], pushE]
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
