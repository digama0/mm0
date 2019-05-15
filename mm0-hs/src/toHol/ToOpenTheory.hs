module ToOpenTheory where

import Control.Monad.RWS.Strict hiding (liftIO)
import qualified Control.Monad.Trans.State as ST
import qualified Data.Map.Strict as M
import Environment (Ident)
import HolTypes

data OTState = OTState {
  otDict :: Int,
  otArrow :: Maybe Int,
  otTrue :: Maybe (Int, Int),
  otSorts :: M.Map Ident Int,
  otEqs :: M.Map [Sort] Int,
  otLamTrue :: M.Map [Sort] Int,
  otTerms :: M.Map Ident Int,
  otDefs :: M.Map Ident Int,
  otTypes :: M.Map SType Int,
  otVars :: M.Map (Ident, SType) Int,
  otThms :: M.Map Ident (Int, [(Ident, Int)])
}

mkOTState :: OTState
mkOTState = OTState 0 Nothing Nothing M.empty M.empty M.empty M.empty M.empty M.empty M.empty M.empty

type OTM = RWS () (Endo [String]) OTState

otToString :: [HDecl] -> [String]
otToString ds = appEndo (snd $ evalRWS (preamble >> mapM_ otDecl ds) () mkOTState) []

preamble :: OTM ()
preamble = do
  emit ["6", "version"]
  emit [show "OT.T"] -- name OT.T
  emit [show "=", "const"]
  let bool = pushSType (SType [] "bool")
  arrows [bool, bool] bool
  emit ["constTerm"] -- const = : bool -> bool -> bool
  pushVar' "x" (SType [] "bool") -- var x : bool
  def >>= ref >> emit ["varTerm", "absTerm"] -- term \(x : bool), (x : bool)
  n <- def
  emit ["appTerm"]
  ref n
  emit ["appTerm"]
  e <- def -- term (\(x : bool), x) = (\(x : bool), x)
  emit ["defineConst", "sym"]
  th <- save -- |- ((\x. x) = (\x. x)) = T
  c <- save -- const T
  ref n >> emit ["refl"] -- |- (\(x : bool), x) = (\(x : bool), x)
  ref th >> emit ["eqMp"]
  tru <- save -- |- T
  modify $ \g -> g {otTrue = Just (c, tru)}

emit :: [String] -> OTM ()
emit s = tell $ Endo (s ++)

ref :: Int -> OTM ()
ref n = emit [show n, "ref"]

def :: OTM Int
def = do
  g <- get
  let n = otDict g
  emit [show n, "def"]
  put $ g {otDict = n + 1}
  return n

save :: OTM Int
save = do n <- def; emit ["pop"]; return n

pushWith :: (OTState -> Maybe Int) -> (Int -> OTState -> OTState) -> OTM () -> OTM ()
pushWith r w go = do
  g <- get
  case r g of
    Just n -> ref n
    Nothing -> go >> def >>= modify . w

pushSort :: Ident -> OTM ()
pushSort x = pushWith (\g -> otSorts g M.!? x)
  (\n g -> g {otSorts = M.insert x n (otSorts g)}) $ do
  emit [show x, "typeOp", "nil", "opType"]

pushArrow :: OTM ()
pushArrow = pushWith otArrow (\n g -> g {otArrow = Just n}) $ do
  emit [show "->", "typeOp"]

arrows :: [OTM ()] -> OTM () -> OTM ()
arrows [] r = r
arrows (m : ms) r =
  pushArrow >> m >> arrows ms r >> emit ["nil", "cons", "cons", "opType"]

pushSType :: SType -> OTM ()
pushSType s@(SType ss t) = pushWith (\g -> otTypes g M.!? s)
  (\n g -> g {otTypes = M.insert s n (otTypes g)})
  (arrows (pushSort <$> ss) (pushSort t))

pushVar' :: Ident -> SType -> OTM ()
pushVar' x t = pushWith (\g -> otVars g M.!? (x, t))
  (\n g -> g {otVars = M.insert (x, t) n (otVars g)}) $ do
  emit [show x] >> pushSType t >> emit ["var"]

pushVar :: M.Map Ident SType -> Ident -> OTM ()
pushVar m x = pushVar' x (m M.! x)

peekVar' :: Ident -> SType -> OTM Int
peekVar' x t = do
  g <- get
  case otVars g M.!? (x, t) of
    Just n -> return n
    Nothing -> pushVar' x t >> save

pushEq :: [Sort] -> OTM ()
pushEq ss = pushWith (\g -> otEqs g M.!? ss)
  (\n g -> g {otEqs = M.insert ss n (otEqs g)}) $ do
    let s = pushSType (SType ss "bool")
    emit [show "=", "const"]
    arrows [s, s] (pushSType (SType [] "bool"))
    emit ["constTerm"]

pushTrue :: OTM ()
pushTrue = otTrue <$> get >>= \(Just (n, _)) -> ref n

pushTriv :: OTM ()
pushTriv = otTrue <$> get >>= \(Just (_, n)) -> ref n

pushLamTrue :: [(Ident, Sort)] -> OTM ()
pushLamTrue xts = let ss = snd <$> xts in
  pushWith (\g -> otLamTrue g M.!? ss)
    (\n g -> g {otLamTrue = M.insert ss n (otLamTrue g)}) (go xts)
  where
  go [] = pushTrue
  go ((x, t) : xts) = pushVar' x (SType [] t) >> go xts >> emit ["absTerm"]

pushAppVars :: M.Map Ident SType -> [Ident] -> OTM ()
pushAppVars m = mapM_ (\x -> pushVar m x >> emit ["varTerm", "appTerm"])

pushAppLams :: M.Map Ident SType -> [SLam] -> OTM ()
pushAppLams m = mapM_ (\l -> pushSLam m l >> emit ["appTerm"])

pushSLam :: M.Map Ident SType -> SLam -> OTM ()
pushSLam m (SLam ss t) = go m ((\(x, s) -> (x, SType [] s)) <$> ss) where
  go :: M.Map Ident SType -> [(Ident, SType)] -> OTM ()
  go m [] = pushTerm m t
  go m ((x, s) : ss) = pushVar' x s >> go (M.insert x s m) ss >> emit ["absTerm"]

pushTerm :: M.Map Ident SType -> Term -> OTM ()
pushTerm m (LVar x) = pushVar m x >> emit ["varTerm"]
pushTerm m (RVar v xs) = pushVar m v >> emit ["varTerm"] >> pushAppVars m xs
pushTerm m (HApp t ls xs) = do
  get >>= ref . (M.! t) . otTerms
  pushAppLams m ls
  pushAppVars m xs

otDecl :: HDecl -> OTM ()
otDecl (HDSort s) = pushSort s >> emit ["pop"]
otDecl (HDTerm x (HType ss t)) = do
  emit [show x, "const"]
  arrows (pushSType <$> ss) (pushSType t)
  emit ["constTerm"]
  n <- save
  modify $ \g -> g {otTerms = M.insert x n (otTerms g)}
otDecl (HDDef x ss xs r t) = do
  emit [show x]
  let ss' = ss ++ ((\(x, s) -> (x, SType [] s)) <$> xs)
  push <- otDef ss' t
  emit ["defineConst"]
  push
  n <- save
  arrows (pushSType . snd <$> ss) (pushSType (SType (snd <$> xs) r))
  emit ["constTerm"]
  c <- save
  modify $ \g -> g {
    otTerms = M.insert x c (otTerms g),
    otDefs = M.insert x n (otDefs g) }
otDecl (HDThm x (TType vs gs r) pr) = do
  emit [show x]
  ns <- mapM (\(x, t) -> (,) x <$> peekVar' x t) vs
  n <- otThm (M.fromList vs) (M.fromList ns) gs r pr
  modify $ \g -> g {
    otThms = M.insert x (n, ns) (otThms g) }

otDef :: [(Ident, SType)] -> Term -> OTM (OTM ())
otDef ss t = go M.empty ss where
  go :: M.Map Ident SType -> [(Ident, SType)] -> OTM (OTM ())
  go m [] = do
    pushTerm m t
    return (return ())
  go m ((x, s) : ss) = do
    pushVar' x s
    push <- go (M.insert x s m) ss
    emit ["absTerm"]
    n <- def
    return $ do
      pushVar' x s
      emit ["varTerm", "refl", "appThm"]
      ref n
      pushVar' x s
      emit ["varTerm", "appTerm", "betaConv", "trans"]

pushGType :: M.Map Ident SType -> GType -> OTM ()
pushGType m (GType xs t) = do
  pushEq (snd <$> xs)
  pushSLam m (SLam xs t)
  emit ["appTerm"]
  pushLamTrue xs
  emit ["appTerm"]

pushGTypes :: M.Map Ident SType -> [GType] -> OTM ()
pushGTypes m [] = emit ["nil"]
pushGTypes m (g:gs) = pushGType m g >> pushGTypes m gs >> emit ["cons"]

otThm :: M.Map Ident SType -> M.Map Ident Int -> [GType] -> GType -> Maybe ([Ident], HProof) -> OTM Int
otThm m ns hs ret pf = do
  case pf of
    Just (xs, p) -> do
      otProof ns (zip xs hs) p
      n <- def
      pushGTypes m hs >> pushGType m ret
      emit ["thm"] >> return n
    Nothing -> do
      pushGTypes m hs >> pushGType m ret
      emit ["axiom"] >> save

otProof :: M.Map Ident Int -> [(Ident, GType)] -> HProof -> OTM ()
otProof = undefined
