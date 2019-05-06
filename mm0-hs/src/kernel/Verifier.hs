module Verifier(verify) where

import Control.Monad.Except
import Control.Monad.RWS.Strict hiding (liftIO)
import Debug.Trace
import Data.Word
import Data.List
import Data.Bits
import Data.Maybe
import Data.Char
import qualified Control.Monad.Trans.State as ST
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Q
import qualified Data.IntMap as I
import qualified Data.Set as S
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString.Lazy.Char8 as BC
import Environment
import ProofTypes
import Util

data VTermData = VTermData {
  vtName :: Maybe Ident, -- ^ Name from the spec
  vtArgs :: [VBinder],   -- ^ Arguments
  vtRet :: VType }       -- ^ Return value sort

data VDefData = VDefData {
  vdDummies :: [SortID], -- ^ Dummy sorts (dummies are numbered after regular vars)
  vdVal :: VExpr }       -- ^ Definition expr

data VThmData = VThmData {
  vaName :: Maybe Ident,    -- ^ Name from the spec
  vaVars :: [VBinder],      -- ^ Sorts of the variables (bound and regular)
  vaDV :: [(VarID, VarID)], -- ^ Disjointness conditions between the variables
  vaHyps :: [VExpr],        -- ^ Hypotheses
  vaRet :: VExpr }          -- ^ Conclusion

-- | Global state of the verifier
data VGlobal = VGlobal {
  -- | Map from SortID to sort data
  vSorts :: Q.Seq (Ident, SortData),
  -- | Map from sort to SortID
  vSortIx :: M.Map Ident SortID,
  -- | Map from TermID to term/def info (for constructing expressions)
  vTerms :: Q.Seq VTermData,
  -- | Map from term to TermID
  vTermIx :: M.Map Ident TermID,
  -- | Map from TermID to def info (for dummy variable replacement)
  vDefs :: I.IntMap VDefData,
  -- | Map from ThmID to axiom/theorem info (for instantiating theorems)
  vThms :: Q.Seq VThmData,
  -- | The current initial segment of the environment that has been checked
  vPos :: Int,
  -- | The collection of outputs (for IO)
  vOutput :: Q.Seq String }

type GVerifyM = RWST () (Endo [String]) VGlobal (Either String)

runGVerifyM :: GVerifyM a -> Environment -> Either String (a, Q.Seq String)
runGVerifyM m e = do
  (a, st, Endo f) <- runRWST m () $ VGlobal Q.empty M.empty Q.empty M.empty I.empty Q.empty 0 Q.empty
  guardError "Not all theorems have been proven" (vPos st == Q.length (eSpec e))
  case f [] of
    [] -> return (a, vOutput st)
    ss -> throwError ("errors:\n" ++ concatMap (\s -> s ++ "\n") ss)

report :: a -> GVerifyM a -> GVerifyM a
report a m = catchError m (\e -> tell (Endo (e :)) >> return a)

checkNotStrict :: VGlobal -> SortID -> Either String ()
checkNotStrict g t = do
  (t, sd) <- fromJustError "sort not found" (vSorts g Q.!? ofSortID t)
  guardError ("cannot bind variable; sort '" ++ t ++ "' is strict") (not (sStrict sd))

withContext :: MonadError String m => String -> m a -> m a
withContext s m = catchError m (\e -> throwError ("while checking " ++ s ++ ":\n" ++ e))

verify :: B.ByteString -> Environment -> Proofs -> Either String (Q.Seq String)
verify spectxt env = \p -> snd <$> runGVerifyM (mapM_ verifyCmd p) env where

  verifyCmd :: ProofCmd -> GVerifyM ()
  verifyCmd (StepSort x) = step >>= \case
    SSort x' sd | x == x' -> modify (\g -> g {
      vSorts = vSorts g Q.|> (x, sd),
      vSortIx = M.insert x (SortID (Q.length (vSorts g))) (vSortIx g) })
    e -> throwError ("incorrect step 'sort " ++ x ++ "', found " ++ show e)
  verifyCmd (StepTerm x) = step >>= \case
    SDecl x' (DTerm args ty) | x == x' -> modify (\g -> g {
      vTerms = vTerms g Q.|> translateTerm (vSortIx g) x args ty,
      vTermIx = M.insert x (TermID (Q.length (vTerms g))) (vTermIx g) })
    e -> throwError ("incorrect step 'term " ++ x ++ "', found " ++ show e)
  verifyCmd (StepAxiom x) = step >>= \case
    SDecl x' (DAxiom args hs ret) | x == x' -> modify (\g -> g {
      vThms = vThms g Q.|> translateAxiom (vSortIx g) (vTermIx g) x args hs ret })
    e -> throwError ("incorrect step 'axiom " ++ x ++ "', found " ++ show e)
  verifyCmd (ProofDef x vs ret ds def st) = do
    g <- get
    let n = TermID (Q.length (vTerms g))
    let name = fromMaybe (show n) x
    report () $ withContext name $ lift $ checkDef g vs ret ds def
    withContext name $ when st $ step >>= \case
      SDecl x' (DDef vs' ret' o) | x == Just x' ->
        guardError "def does not match declaration" $
          matchDef (vTermIx g) (vSortIx g) vs ret ds vs' ret' def o
      e -> throwError ("incorrect def step, found " ++ show e)
    modify (\g -> g {
      vTerms = vTerms g Q.|> VTermData x vs ret,
      vTermIx = maybe (vTermIx g) (\x' -> M.insert x' n (vTermIx g)) x,
      vDefs = I.insert (ofTermID n) (VDefData ds def) (vDefs g) })
  verifyCmd (ProofThm x vs hs ret unf ds pf st) = do
    g <- get
    let n = ThmID (Q.length (vThms g))
    let name = fromMaybe (show n) x
    report () $ withContext name $ lift $ checkThm g vs hs ret unf ds pf
    withContext name $ when st $ step >>= \case
      SThm x' vs' hs' ret' | x == Just x' ->
        guardError "theorem does not match declaration" $
          matchThm (vTermIx g) (vSortIx g) vs hs ret vs' hs' ret'
      e -> throwError ("incorrect theorem step, found " ++ show e)
    modify (\g -> g {
      vThms = vThms g Q.|> VThmData x vs (makeDV vs) hs ret })
  verifyCmd (StepInout (VIKString out)) = step >>= \case
    SInout (IOKString False e) | not out -> verifyInputString spectxt e
    SInout (IOKString True e) | out -> verifyOutputString spectxt e
    _ | out -> throwError "incorrect output step"
    _ -> throwError "incorrect input step"

  step :: GVerifyM Spec
  step = do
    n <- state (\g -> (vPos g, g {vPos = vPos g + 1}))
    fromJustError "nothing more to prove" (eSpec env Q.!? n)

  checkDef :: VGlobal -> [VBinder] -> VType -> [SortID] ->
    VExpr -> Either String ()
  checkDef g vs (VType ret rs) ds def = do
    let ctx = Q.fromList vs
    checkBinders g ctx vs
    mapM_ (\v -> case ctx Q.!? ofVarID v of
      Just (VBound _) -> return ()
      _ -> throwError "undeclared variable in dependency") rs
    (ri, sd) <- fromJustError "sort not found" (vSorts g Q.!? ofSortID ret)
    guardError ("cannot declare term for pure sort '" ++ ri ++ "'") (not (sPure sd))
    mapM_ (checkNotStrict g) ds
    let ctx' = ctx <> Q.fromList (VBound <$> ds)
    (ret', rs') <- defcheckExpr (vTerms g) ctx' def
    guardError "type error" (ret == ret')
    let fv = S.difference rs' (S.fromList rs)
    S.foldl' (\r v -> r >> case ctx' Q.!? ofVarID v of
      Just (VBound s) -> do
        (_, sd') <- fromJustError "sort not found" (vSorts g Q.!? ofSortID s)
        guardError "unaccounted free variable" (not (sFree sd'))
      _ -> throwError "undeclared variable in dependency") (return ()) fv

  defcheckExpr :: Q.Seq VTermData -> Q.Seq VBinder -> VExpr -> Either String (SortID, S.Set VarID)
  defcheckExpr terms ctx = defcheckExpr' where
    defcheckExpr' (VVar v) = case ctx Q.!? ofVarID v of
      Nothing -> throwError "undeclared variable in def expr"
      Just (VBound s) -> return (s, S.singleton v)
      Just (VReg s vs) -> return (s, S.fromList vs)
    defcheckExpr' (VApp t es) = do
      VTermData _ args (VType ret rs) <- fromJustError "unknown term in def expr" (terms Q.!? ofTermID t)
      (m, ev) <- withContext (showVExpr terms (VApp t es)) $ defcheckArgs args es
      return (ret, ev <> S.fromList ((\v -> m I.! ofVarID v) <$> rs))

    defcheckArgs :: [VBinder] -> [VExpr] -> Either String (I.IntMap VarID, S.Set VarID)
    defcheckArgs args es = go args es 0 I.empty S.empty where
      go [] [] _ m ev = return (m, ev)
      go (VBound s : args) (VVar v : es) n m ev = case ctx Q.!? ofVarID v of
        Just (VBound s') | s == s' ->
          go args es (n+1) (I.insert n v m) ev
        _ -> throwError "non-bound variable in BV slot"
      go (VBound _ : args) (_ : es) _ _ _ =
        throwError "non-bound variable in BV slot"
      go (VReg s vs : args) (e : es) n m ev = do
        (s', ev') <- defcheckExpr' e
        guardError "type mismatch" (s == s')
        let ev'' = foldl' (\ev' v -> S.delete (m I.! ofVarID v) ev') ev' vs
        go args es (n+1) m (ev <> ev'')
      go _ _ _ _ _ | length args == length es =
        throwError ("term arguments don't match substitutions:" ++
          " args =" ++ fst (ppBinders () args 0)
          (", subst = " ++ showVExprList terms es))
      go _ _ _ _ _ = throwError ("expected " ++ show (length args) ++
        " arguments, got " ++ show (length es))

  matchDef :: M.Map Ident TermID -> M.Map Ident SortID -> [VBinder] -> VType -> [SortID] ->
    [PBinder] -> DepType -> VExpr -> Maybe (M.Map Ident Ident, SExpr) -> Bool
  matchDef termIx sortIx vs (VType ret rs) ds args (DepType t ts) def o =
    let (args', n, varIx) = trBinders sortIx args in
    vs == args' && sortIx M.! t == ret && ((varIx M.!) <$> ts) == rs &&
    case o of
      Nothing -> True
      Just (m, expr) -> ((sortIx M.!) <$> M.elems m) == ds &&
        matchExpr termIx (trDummies n varIx (M.keys m)) def expr
    where
    trDummies :: Int -> M.Map Ident VarID -> [Ident] -> M.Map Ident VarID
    trDummies _ m [] = m
    trDummies n m (v:vs) = trDummies (n+1) (M.insert v (VarID n) m) vs

  checkThm :: VGlobal -> [VBinder] -> [VExpr] -> VExpr -> [TermID] ->
    [SortID] -> ProofTree -> Either String ()
  checkThm g vs hs ret unf ds pf = do
    let ctx = Q.fromList vs
    mapM_ (typecheckProvable g ctx) hs
    typecheckProvable g ctx ret
    ((hs', ret'), ctx') <- case unf of
      [] -> return ((hs, ret), ctx)
      _ -> let unfold = unfoldExpr (vDefs g) (S.fromList unf) in
        ST.runStateT ((,) <$> mapM unfold hs <*> unfold ret) ctx
    let ctx'' = ctx' <> Q.fromList (VBound <$> ds)
    ret'' <- verifyProof g ctx'' hs' pf
    guardError "theorem did not prove what it claimed" (ret' == ret'')

  typecheckExpr :: Q.Seq VTermData -> Q.Seq VBinder -> VExpr -> Either String SortID
  typecheckExpr terms ctx = typecheckExpr' where
    typecheckExpr' (VVar v) = case ctx Q.!? ofVarID v of
      Nothing -> throwError "undeclared variable in def expr"
      Just (VBound s) -> return s
      Just (VReg s vs) -> return s
    typecheckExpr' (VApp t es) = do
      VTermData _ args (VType ret _) <- fromJustError "unknown term in def expr" (terms Q.!? ofTermID t)
      typecheckArgs args es >> return ret

    typecheckArgs :: [VBinder] -> [VExpr] -> Either String ()
    typecheckArgs [] [] = return ()
    typecheckArgs (VBound s : args) (VVar v : es) = case ctx Q.!? ofVarID v of
      Just (VBound s') | s == s' -> typecheckArgs args es
      _ -> throwError "non-bound variable in BV slot"
    typecheckArgs (VBound _ : args) (_ : es) =
      throwError "non-bound variable in BV slot"
    typecheckArgs (VReg s vs : args) (e : es) = do
      s' <- typecheckExpr' e
      guardError "type mismatch" (s == s')
      typecheckArgs args es
    typecheckArgs _ _ = throwError "term arguments don't match substitutions"

  typecheckProvable :: VGlobal -> Q.Seq VBinder -> VExpr -> Either String ()
  typecheckProvable g ctx expr = do
    s <- typecheckExpr (vTerms g) ctx expr
    (si, sd) <- fromJustError "sort not found" (vSorts g Q.!? ofSortID s)
    guardError ("non-provable sort '" ++ si ++ "' in theorem") (sProvable sd)

  unfoldExpr :: I.IntMap VDefData -> S.Set TermID -> VExpr -> ST.StateT (Q.Seq VBinder) (Either String) VExpr
  unfoldExpr defs u = go where
    go (VApp t es) | t `S.member` u = do
      es' <- mapM go es
      VDefData ud uv <- fromJustError "could not unfold non-def" (defs I.!? ofTermID t)
      subst <- buildSubst (Q.fromList es') ud
      return (substExpr subst uv)
    go (VApp t es) = VApp t <$> mapM go es
    go e = return e

  buildSubst :: Q.Seq VExpr -> [SortID] -> ST.StateT (Q.Seq VBinder) (Either String) (Q.Seq VExpr)
  buildSubst m [] = return m
  buildSubst m (d:ds) = ST.StateT $ \ctx ->
    ST.runStateT (buildSubst (m Q.|> VVar (VarID (Q.length ctx))) ds)
      (ctx Q.|> VBound d)

  matchThm :: M.Map Ident TermID -> M.Map Ident SortID ->
    [VBinder] -> [VExpr] -> VExpr -> [PBinder] -> [SExpr] -> SExpr -> Bool
  matchThm termIx sortIx vs hs ret args hs' ret' =
    let (args', n, varIx) = trBinders sortIx args in
    vs == args' &&
    matchExprs termIx varIx hs hs' &&
    matchExpr termIx varIx ret ret'

  matchExpr :: M.Map Ident TermID -> M.Map Ident VarID -> VExpr -> SExpr -> Bool
  matchExpr _ varIx (VVar v) (SVar x) = varIx M.! x == v
  matchExpr termIx varIx (VApp t es) (App x ss) =
    termIx M.! x == t && matchExprs termIx varIx es ss
  matchExpr _ _ _ _ = False

  matchExprs :: M.Map Ident TermID -> M.Map Ident VarID -> [VExpr] -> [SExpr] -> Bool
  matchExprs termIx varIx = go where
    go [] [] = True
    go (e:es) (s:ss) = matchExpr termIx varIx e s && go es ss
    go _ _ = False

  checkBinders :: VGlobal -> Q.Seq VBinder -> [VBinder] -> Either String ()
  checkBinders g ctx = go 0 where
    go n [] = return ()
    go n (VBound t : bis) = do
      checkNotStrict g t
      go (n+1) bis
    go n (VReg t ts : bis) = do
      guardError "undeclared variable in dependency" $
        all (\(VarID v) -> v < n && isBound (Q.index ctx v)) ts
      guardError "sort not found" (ofSortID t < Q.length (vSorts g))
      go (n+1) bis

trBinders :: M.Map Ident SortID -> [PBinder] -> ([VBinder], Int, M.Map Ident VarID)
trBinders sortIx = go 0 M.empty where
  go n m [] = ([], n, m)
  go n m (PBound v t : bis) =
    let (bis', n', m') = go (n+1) (M.insert v (VarID n) m) bis in
    (VBound (sortIx M.! t) : bis', n', m')
  go n m (PReg v (DepType t ts) : bis) =
    let (bis', n', m') = go (n+1) (M.insert v (VarID n) m) bis in
    (VReg (sortIx M.! t) ((m M.!) <$> ts) : bis', n', m')

translateTerm :: M.Map Ident SortID -> Ident -> [PBinder] -> DepType -> VTermData
translateTerm sortIx = \x args (DepType t ts) ->
  let (args', n, varIx) = trBinders sortIx args in
  VTermData (Just x) args' $
    VType (sortIx M.! t) ((varIx M.!) <$> ts)

translateAxiom :: M.Map Ident SortID -> M.Map Ident TermID ->
  Ident -> [PBinder] -> [SExpr] -> SExpr -> VThmData
translateAxiom sortIx termIx x args hs ret =
  let (args', _, varIx) = trBinders sortIx args in
  VThmData (Just x) args' (makeDV args')
    (trExpr termIx varIx <$> hs) (trExpr termIx varIx ret)

trExpr :: M.Map Ident TermID -> M.Map Ident VarID -> SExpr -> VExpr
trExpr termIx varIx = go where
  go (SVar v) = VVar (varIx M.! v)
  go (App t es) = VApp (termIx M.! t) (go <$> es)

makeDV :: [VBinder] -> [(VarID, VarID)]
makeDV = go 0 [] where
  go :: Int -> [VarID] -> [VBinder] -> [(VarID, VarID)]
  go n bs [] = []
  go n bs (VReg _ ts : bis) =
    let s = S.fromList ts in
    ((,) (VarID n) <$> (filter (`S.notMember` s) bs)) ++ go (n+1) bs bis
  go n bs (VBound _ : bis) = ((,) (VarID n) <$> bs) ++ go (n+1) (VarID n : bs) bis

data StackSlot =
  -- | A bound variable.
    SSBound SortID VarID
  -- | A term with the given sort. The bit set gives the variables used in the expression.
  | SSExpr SortID VExpr VBitSet
  -- | A proof of a term
  | SSProof VExpr
  deriving (Show, Eq)

ofSSExpr :: StackSlot -> Maybe (SortID, VExpr, VBitSet)
ofSSExpr (SSExpr s e b) = Just (s, e, b)
ofSSExpr (SSBound s v) = Just (s, VVar v, bit (ofVarID v))
ofSSExpr _ = Nothing

type VBitSet = Word64

ltBitSize :: Int -> Bool
ltBitSize n = case bitSizeMaybe (undefined :: VBitSet) of
  Nothing -> True
  Just k -> n < k

-- | Local state of the verifier (inside a proof)
data VState = VState {
  -- | Map from HeapID to proven expressions
  vHeap :: Q.Seq StackSlot } deriving (Show)

type VerifyM = ST.StateT VState (Either String)

verifyProof :: VGlobal -> Q.Seq VBinder -> [VExpr] -> ProofTree -> Either String VExpr
verifyProof g = \ctx hs cs -> do
  guardError "variable limit (64) exceeded" (ltBitSize (Q.length ctx))
  let heap = Q.foldlWithIndex (\s n b -> s Q.|> varToStackSlot n b) Q.empty ctx
  let heap' = foldl (\s h -> s Q.|> SSProof h) heap hs
  ST.evalStateT (verifyTree cs) (VState heap') >>= \case
    SSProof e -> return e
    s -> throwError ("Bad proof state " ++ show s)
  where
  varToStackSlot :: Int -> VBinder -> StackSlot
  varToStackSlot n (VBound s) = SSBound s (VarID n)
  varToStackSlot n (VReg s vs) = SSExpr s (VVar (VarID n))
    (foldl' (\bs (VarID v) -> bs .|. bit v) 0 vs)

  verifyTree :: ProofTree -> VerifyM StackSlot
  verifyTree (Load (VarID h)) = do
    VState heap <- get
    fromJustError "index out of bounds" (heap Q.!? h)
  verifyTree (Save p) = do
    ss <- verifyTree p
    modify $ \(VState heap) -> VState (heap Q.|> ss)
    return ss
  verifyTree (VTerm t es) = do
    sss <- mapM verifyTree es
    VTermData _ args (VType ret _) <- fromJustError "term not found" (vTerms g Q.!? ofTermID t)
    (es, hs, b) <- verifyArgs 0 (.|.) args sss
    guardError "argument number mismatch" (null hs)
    return (SSExpr ret (VApp t es) b)
  verifyTree (VThm t ts) = do
    vs' <- mapM verifyTree ts
    VThmData x args dv hs ret <- fromJustError "theorem not found" (vThms g Q.!? ofThmID t)
    withContext ("step " ++ fromMaybe (show t) x) $ do
      (es, hs', b) <- verifyArgs Q.empty (Q.<|) args vs'
      let subst = Q.fromList es
      mapM_ (\(VarID v1, VarID v2) ->
        guardError (let terms = vTerms g in
            "disjoint variable violation (" ++
            showVExpr terms (Q.index subst v1) ++ " / " ++
            showVExpr terms (Q.index subst v2) ++ ")")
          (Q.index b v1 .&. Q.index b v2 == 0)) dv
      verifyHyps (Q.fromList es) hs hs'
      return (SSProof (substExpr subst ret))
  verifyTree Sorry = throwError "? found in proof"

  verifyArgs :: a -> (VBitSet -> a -> a) -> [VBinder] -> [StackSlot] -> VerifyM ([VExpr], [StackSlot], a)
  verifyArgs a f = go where
    go [] sss = return ([], sss, a)
    go (_:_) [] = throwError "argument number mismatch"
    go (VBound s' : bs) (SSBound s v : sss) = do
      guardError "type mismatch" (s == s')
      (\(l, ss', b) -> (VVar v : l, ss', f (bit (ofVarID v)) b)) <$> go bs sss
    go (VBound _: _) (_ : _) = throwError "non-bound variable in BV slot"
    go (VReg s' _ : bs) (ss : sss) = do
      (s, e, b) <- fromJustError "bad stack slot" (ofSSExpr ss)
      guardError "type mismatch" (s == s')
      (\(l, ss', b') -> (e : l, ss', f b b')) <$> go bs sss

  verifyHyps :: Q.Seq VExpr -> [VExpr] -> [StackSlot] -> VerifyM ()
  verifyHyps subst = go where
    go [] [] = return ()
    go (e : es) (SSProof p : sss) = do
      guardError (let terms = vTerms g in
          "substitution to hypothesis does not match theorem\n" ++
          showVExpr terms e ++ showVExprList terms es ++ " = " ++
          showVExpr terms (substExpr subst e) ++ " != " ++
          showVExpr terms p)
        (substExpr subst e == p)
      go es sss
    go _ _ = throwError "bad stack slot reference or argument mismatch"

--------------------------------------------------
-- Input/Output for 'string' (optional feature) --
--------------------------------------------------

data StringPart = IFull B.ByteString | IHalf Word8 B.ByteString
type StringInM = StringPart -> Either String StringPart

spUncons :: StringPart -> Maybe (Word8, StringPart)
spUncons (IFull s) = case B.uncons s of
  Nothing -> Nothing
  Just (c, s) -> Just (shiftR c 4, IHalf (c .&. 15) s)
spUncons (IHalf c s) = Just (c, IFull s)

spRest :: StringPart -> B.ByteString
spRest (IFull s) = s
spRest (IHalf _ s) = s

spLen :: StringPart -> Int
spLen (IFull s) = fromIntegral (B.length s)
spLen (IHalf _ s) = fromIntegral (B.length s + 1)

toHex :: Word8 -> Char
toHex i = chr $ (if i < 10 then ord '0' else ord 'a' - 10) + fromIntegral i

verifyInputString :: B.ByteString -> SExpr -> GVerifyM ()
verifyInputString spectxt e = do
  g <- get
  procs <- foldM
    (\m (s, f) -> do
      TermID n <- fromJustError
        ("term '" ++ s ++ "' not found for string i/o") (vTermIx g M.!? s)
      return (I.insert n f m))
    I.empty proclist
  lift $ unify (vTerms g) (vDefs g) procs (trExpr (vTermIx g) M.empty e)
  where
  proclist :: [(String, (VExpr -> StringInM) -> [VExpr] -> StringInM)]
  proclist =
    ("s0", \_ [] s -> return s) :
    ("s1", \f [e] -> f e) :
    ("sadd", \f [e1, e2] s -> f e1 s >>= f e2) :
    ("ch", \f [e1, e2] s -> f e1 s >>= f e2) :
    map (\i -> ('x' : toHex i : [],
      \_ [] s -> case spUncons s of
        Nothing -> throwError "EOF"
        Just (c, s') -> do
          guardError (mismatch s) (c == fromIntegral i)
          return s')) [0..15]

  unify :: Q.Seq VTermData -> I.IntMap VDefData ->
    I.IntMap ((VExpr -> StringInM) -> [VExpr] -> StringInM) ->
    VExpr -> Either String ()
  unify terms defs procs = \e -> go [] e (IFull spectxt) >>= \case
    (IFull s) | B.null s -> return ()
    s' -> throwError (mismatch s')
    where

    go :: [Q.Seq VExpr] -> VExpr -> StringInM
    go [] (VVar n) s = error "free variable found"
    go (es : stk) (VVar (VarID n)) s = go stk (Q.index es n) s
    go stk (VApp t es) s = do
      case defs I.!? ofTermID t of
        Just (VDefData [] val) -> go (Q.fromList es : stk) val s
        Just (VDefData _ _) -> throwError ("definition " ++
          showVExpr terms (VApp t []) ++ " has dummy variables")
        Nothing -> case procs I.!? ofTermID t of
          Just f -> f (go stk) es s
          Nothing -> throwError ("term '" ++ showVExpr terms (VApp t []) ++ "' not supported")

  mismatch s = "input mismatch at char " ++
    show (fromIntegral (B.length spectxt) - spLen s) ++ ": rest = '" ++
      BC.unpack (B.take 10 (spRest s)) ++
      if B.length (spRest s) <= 10 then "'" else "'..."

data OStringPart = OString (String -> String) | OHex Word8
type StringOutM = Either String OStringPart

verifyOutputString :: B.ByteString -> SExpr -> GVerifyM ()
verifyOutputString s e = do
  g <- get
  procs <- foldM
    (\m (s, f) -> do
      TermID n <- fromJustError
        ("term '" ++ s ++ "' not found for string i/o") (vTermIx g M.!? s)
      return (I.insert n f m))
    I.empty proclist
  lift (toString (vTerms g) (vDefs g) procs (trExpr (vTermIx g) M.empty e)) >>= \case
    OString out -> modify (\g -> g {vOutput = vOutput g Q.|> out []})
    OHex _ -> throwError "impossible, check axioms"
  where
  proclist :: [(String, (VExpr -> StringOutM) -> [VExpr] -> StringOutM)]
  proclist =
    ("s0", \_ [] -> return (OString id)) :
    ("s1", \f [e] -> f e) :
    ("sadd", \f [e1, e2] ->
      let app (OString s1) (OString s2) = OString (s1 . s2)
          app _ _ = error "impossible, check axioms" in
      app <$> f e1 <*> f e2) :
    ("ch", \f [e1, e2] ->
      let app (OHex h1) (OHex h2) =
            OString (chr (fromIntegral (shiftL h1 4 .|. h2)) :)
          app _ _ = error "impossible, check axioms" in
      app <$> f e1 <*> f e2) :
    map (\i -> ('x' : toHex i : [], \_ [] -> return (OHex i))) [0..15]

  toString :: Q.Seq VTermData -> I.IntMap VDefData ->
    I.IntMap ((VExpr -> StringOutM) -> [VExpr] -> StringOutM) ->
    VExpr -> StringOutM
  toString terms defs procs = go [] where
    go :: [Q.Seq VExpr] -> VExpr -> StringOutM
    go [] (VVar n) = error "free variable found"
    go (es : stk) (VVar (VarID n)) = go stk (Q.index es n)
    go stk (VApp t es) = do
      case defs I.!? ofTermID t of
        Just (VDefData [] val) -> go (Q.fromList es : stk) val
        Just (VDefData _ _) -> throwError ("definition " ++
          showVExpr terms (VApp t []) ++ " has dummy variables")
        Nothing -> case procs I.!? ofTermID t of
          Just f -> f (go stk) es
          Nothing -> throwError ("term '" ++ showVExpr terms (VApp t []) ++ "' not supported")

-----------------------------------------------
-- Expression printing (for error reporting) --
-----------------------------------------------

showVExpr :: Q.Seq VTermData -> VExpr -> String
showVExpr terms e = showsVExpr terms e []

showVExprList :: Q.Seq VTermData -> [VExpr] -> String
showVExprList terms es = showList' (showsVExpr terms) es []

showsVExpr :: Q.Seq VTermData -> VExpr -> ShowS
showsVExpr terms = go 0 where
  go n (VVar v) r = showsPrec n v r
  go n (VApp t []) r = showTerm t r
  go n (VApp t es) r =
    let f r = showTerm t (foldr (\e r -> ' ' : go 1 e r) r es) in
    if n == 0 then f r else '(' : f (')' : r)

  showTerm :: TermID -> ShowS
  showTerm t r = case terms Q.!? ofTermID t of
    Just (VTermData (Just x) _ _) -> x ++ r
    Just (VTermData Nothing _ _) -> showsPrec 0 t r
    Nothing -> '?' : showsPrec 0 t r

-- from haskell core
showList' :: (a -> ShowS) ->  [a] -> ShowS
showList' _     []     s = "[]" ++ s
showList' showx (x:xs) s = '[' : showx x (showl xs)
  where
    showl []     = ']' : s
    showl (y:ys) = ',' : showx y (showl ys)
