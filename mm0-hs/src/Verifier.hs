module Verifier() where

import Control.Monad.Except
import Control.Monad.Trans.State
import Data.Word
import Data.List
import Data.Bits
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Q
import qualified Data.IntMap as I
import AST (SortData(..), Ident, DepType(..))
import Environment
import Util

newtype SortID = SortID {ofSortID :: Int} deriving (Eq)
newtype TermID = TermID {ofTermID :: Int} deriving (Eq)
newtype ThmID = ThmID {ofThmID :: Int}
newtype VarID = VarID {ofVarID :: Int} deriving (Eq, Ord)

data VType = VType SortID [VarID]
data VBinder = VBound SortID | VReg SortID [VarID]
data VExpr = VVar VarID | VApp TermID [VExpr] deriving (Eq)

data VTermData = VTermData {
  vtName :: Maybe Ident, -- ^ Name from the spec
  vtArgs :: [VBinder],   -- ^ Arguments
  vtRet :: VType }      -- ^ Return value sort

data VDefData = VDefData {
  vdDummies :: [SortID], -- ^ Dummy sorts (dummies are numbered after regular vars)
  vdVal :: VExpr }       -- ^ Definition expr

data VAssrtData = VAssrtData {
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
  vThms :: Q.Seq VAssrtData,
  -- | The current initial segment of the environment that has been checked
  vPos :: Int }

type GVerifyM = StateT VGlobal (Either String)

runGVerifyM :: GVerifyM a -> Environment -> Either String a
runGVerifyM m e = do
  (a, st) <- runStateT m $ VGlobal Q.empty M.empty Q.empty M.empty I.empty Q.empty 0
  guardError "Not all theorems have been proven" (vPos st == Q.length (eSpec e))
  return a

data VDBinder = VDBound SortID | VDReg SortID (S.Set VarID) deriving (Eq)

toVBinder :: VDBinder -> VBinder
toVBinder (VDBound s) = VBound s
toVBinder (VDReg s vs) = VReg s (S.elems vs)

isBound :: VDBinder -> Bool
isBound (VDBound _) = True
isBound _ = False

checkNotStrict :: VGlobal -> SortID -> Either String ()
checkNotStrict g t = do
  (t, sd) <- fromJustError "sort not found" (vSorts g Q.!? ofSortID t)
  guardError ("cannot bind variable; sort '" ++ t ++ "' is strict") (not (sStrict sd))

type Proofs = [ProofCmd]
data ProofCmd =
    StepSort Ident
  | StepTerm Ident
  | StepAxiom Ident
  | ProofDef {
      pdArgs :: [VDBinder],   -- ^ The arguments to the definition
      pdRet :: VType,         -- ^ The return type
      pdDummies :: [SortID],  -- ^ The types of the dummies
      pdVal :: VExpr,         -- ^ The value of the definition
      pdStep :: Maybe Ident } -- ^ The name of the definition in the spec
  | ProofThm {
      ptVar :: [VDBinder],      -- ^ The variables
      ptHyps :: [VExpr],        -- ^ The hypotheses
      ptRet :: VExpr,           -- ^ The return type
      ptUnfold :: Maybe TermID, -- ^ Which definition to unfold in the statement
      ptDummies :: [SortID],    -- ^ The types of the dummies
      ptProof :: [LocalCmd],    -- ^ The actual proof
      ptStep :: Maybe Ident }   -- ^ The name of the theorem in the spec

verify :: Environment -> Proofs -> Either String ()
verify env = \p -> runGVerifyM (mapM_ verifyCmd p) env where

  verifyCmd :: ProofCmd -> GVerifyM ()
  verifyCmd (StepSort x) = step >>= \case
    SSort x' sd | x == x' -> modify (\g -> g {
      vSorts = vSorts g Q.|> (x, sd),
      vSortIx = M.insert x (SortID (Q.length (vSorts g))) (vSortIx g) })
    _ -> throwError "incorrect sort step"
  verifyCmd (StepTerm x) = step >>= \case
    SDecl x' (DTerm args ty) | x == x' -> modify (\g -> g {
      vTerms = vTerms g Q.|> translateTerm (vSortIx g) x args ty,
      vTermIx = M.insert x (TermID (Q.length (vTerms g))) (vTermIx g) })
    _ -> throwError "incorrect term step"
  verifyCmd (StepAxiom x) = step >>= \case
    SDecl x' (DAxiom args hs ret) | x == x' -> modify (\g -> g {
      vThms = vThms g Q.|> translateAxiom (vSortIx g) (vTermIx g) x args hs ret })
    _ -> throwError "incorrect axiom step"
  verifyCmd (ProofDef vs ret ds def st) = do
    g <- get
    lift $ checkDef g vs ret ds def
    case st of
      Nothing -> return ()
      Just x -> step >>= \case
        SDecl x' (DDef vs' ret' o) | x == x' ->
          guardError ("def '" ++ x ++ "' does not match declaration") $
            matchDef (vTermIx g) (vSortIx g) vs ret ds vs' ret' def o
        _ -> throwError "incorrect def step"
  verifyCmd (ProofThm vs hs ret unf ds pf st) = do
    g <- get
    lift $ checkThm g vs hs ret unf ds pf
    case st of
      Nothing -> return ()
      Just x -> step >>= \case
        SThm x' vs' hs' ret' | x == x' ->
          guardError ("theorem '" ++ x ++ "' does not match declaration") $
            matchThm (vTermIx g) (vSortIx g) vs hs ret vs' hs' ret'
        _ -> throwError "incorrect theorem step"

  step :: GVerifyM Spec
  step = do
    n <- state (\g -> (vPos g, g {vPos = vPos g + 1}))
    fromJustError "nothing more to prove" (eSpec env Q.!? n)

  checkDef :: VGlobal -> [VDBinder] -> VType -> [SortID] ->
    VExpr -> Either String ()
  checkDef g vs (VType ret rs) ds def = do
    let ctx = Q.fromList vs
    checkBinders g ctx vs
    mapM_ (\v -> case ctx Q.!? ofVarID v of
      Just (VDBound _) -> return ()
      _ -> throwError "undeclared variable in dependency") rs
    (ri, sd) <- fromJustError "sort not found" (vSorts g Q.!? ofSortID ret)
    guardError ("cannot declare term for pure sort '" ++ ri ++ "'") (not (sPure sd))
    mapM_ (checkNotStrict g) ds
    let ctx' = ctx <> Q.fromList (VDBound <$> ds)
    (ret', rs') <- defcheckExpr (vTerms g) ctx' def
    guardError "type error" (ret == ret')
    guardError "unaccounted free variables" (S.isSubsetOf rs' (S.fromList rs))

  defcheckExpr :: Q.Seq VTermData -> Q.Seq VDBinder -> VExpr -> Either String (SortID, S.Set VarID)
  defcheckExpr terms ctx = defcheckExpr' where
    defcheckExpr' (VVar v) = case ctx Q.!? ofVarID v of
      Nothing -> throwError "undeclared variable in def expr"
      Just (VDBound s) -> return (s, S.singleton v)
      Just (VDReg s vs) -> return (s, vs)
    defcheckExpr' (VApp t es) = do
      VTermData _ args (VType ret rs) <- fromJustError "unknown term in def expr" (terms Q.!? ofTermID t)
      (m, ev) <- defcheckArgs args es
      return (ret, ev <> S.fromList ((\v -> m I.! ofVarID v) <$> rs))

    defcheckArgs :: [VBinder] -> [VExpr] -> Either String (I.IntMap VarID, S.Set VarID)
    defcheckArgs args es = go args es 0 I.empty S.empty where
      go [] [] _ m ev = return (m, ev)
      go (VBound s : args) (VVar v : es) n m ev = case ctx Q.!? ofVarID v of
        Just (VDBound s') | s == s' ->
          go args es (n+1) (I.insert n v m) ev
        _ -> throwError "non-bound variable in BV slot"
      go (VBound _ : args) (_ : es) _ _ _ =
        throwError "non-bound variable in BV slot"
      go (VReg s vs : args) (e : es) n m ev = do
        (s', ev') <- defcheckExpr' e
        guardError "type mismatch" (s == s')
        let ev'' = foldl' (\ev' v -> S.delete (m I.! ofVarID v) ev') ev' vs
        go args es (n+1) m (ev <> ev'')
      go _ _ _ _ _ = throwError "term arguments don't match substitutions"

  matchDef :: M.Map Ident TermID -> M.Map Ident SortID -> [VDBinder] -> VType -> [SortID] ->
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

  checkThm :: VGlobal -> [VDBinder] -> [VExpr] -> VExpr -> Maybe TermID ->
    [SortID] -> [LocalCmd] -> Either String ()
  checkThm g vs hs ret unf ds pf = do
    let ctx = Q.fromList vs
    mapM_ (typecheckProvable g ctx) hs
    typecheckProvable g ctx ret
    ((hs', ret'), ctx') <- case unf of
      Nothing -> return ((hs, ret), ctx)
      Just u -> do
        dd <- fromJustError "could not unfold non-def" (vDefs g I.!? ofTermID u)
        let unfold = unfoldExpr u dd
        runStateT ((,) <$> mapM unfold hs <*> unfold ret) ctx
    let ctx'' = ctx' <> Q.fromList (VDBound <$> ds)
    ret'' <- verifyProof g ctx'' hs' pf
    guardError "theorem did not prove what it claimed" (ret' == ret'')

  typecheckExpr :: Q.Seq VTermData -> Q.Seq VDBinder -> VExpr -> Either String SortID
  typecheckExpr terms ctx = typecheckExpr' where
    typecheckExpr' (VVar v) = case ctx Q.!? ofVarID v of
      Nothing -> throwError "undeclared variable in def expr"
      Just (VDBound s) -> return s
      Just (VDReg s vs) -> return s
    typecheckExpr' (VApp t es) = do
      VTermData _ args (VType ret _) <- fromJustError "unknown term in def expr" (terms Q.!? ofTermID t)
      typecheckArgs args es >> return ret

    typecheckArgs :: [VBinder] -> [VExpr] -> Either String ()
    typecheckArgs [] [] = return ()
    typecheckArgs (VBound s : args) (VVar v : es) = case ctx Q.!? ofVarID v of
      Just (VDBound s') | s == s' -> typecheckArgs args es
      _ -> throwError "non-bound variable in BV slot"
    typecheckArgs (VBound _ : args) (_ : es) =
      throwError "non-bound variable in BV slot"
    typecheckArgs (VReg s vs : args) (e : es) = do
      s' <- typecheckExpr' e
      guardError "type mismatch" (s == s')
      typecheckArgs args es
    typecheckArgs _ _ = throwError "term arguments don't match substitutions"

  typecheckProvable :: VGlobal -> Q.Seq VDBinder -> VExpr -> Either String ()
  typecheckProvable g ctx expr = do
    s <- typecheckExpr (vTerms g) ctx expr
    (si, sd) <- fromJustError "sort not found" (vSorts g Q.!? ofSortID s)
    guardError ("non-provable sort '" ++ si ++ "' in theorem") (sProvable sd)

  unfoldExpr :: TermID -> VDefData -> VExpr -> StateT (Q.Seq VDBinder) (Either String) VExpr
  unfoldExpr u (VDefData ud uv) = go where
    go (VApp t es) | t == u = do
      es' <- mapM go es
      subst <- buildSubst (Q.fromList es') ud
      return (substExpr subst uv)
    go (VApp t es) = VApp t <$> mapM go es
    go e = return e

  buildSubst :: Q.Seq VExpr -> [SortID] -> StateT (Q.Seq VDBinder) (Either String) (Q.Seq VExpr)
  buildSubst m [] = return m
  buildSubst m (d:ds) = StateT $ \ctx ->
    runStateT (buildSubst (m Q.|> VVar (VarID (Q.length ctx))) ds)
      (ctx Q.|> VDBound d)

  matchThm :: M.Map Ident TermID -> M.Map Ident SortID ->
    [VDBinder] -> [VExpr] -> VExpr -> [PBinder] -> [SExpr] -> SExpr -> Bool
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

  checkBinders :: VGlobal -> Q.Seq VDBinder -> [VDBinder] -> Either String ()
  checkBinders g ctx = go 0 where
    go n [] = return ()
    go n (VDBound t : bis) = do
      checkNotStrict g t
      go (n+1) bis
    go n (VDReg t ts : bis) = do
      guardError "undeclared variable in dependency" $
        all (\(VarID v) -> v < n && isBound (Q.index ctx v)) ts
      guardError "sort not found" (ofSortID t < Q.length (vSorts g))
      go (n+1) bis

trBinders :: M.Map Ident SortID -> [PBinder] -> ([VDBinder], Int, M.Map Ident VarID)
trBinders sortIx = go 0 M.empty where
  go n m [] = ([], n, m)
  go n m (PBound v t : bis) =
    let (bis', n', m') = go (n+1) (M.insert v (VarID n) m) bis in
    (VDBound (sortIx M.! t) : bis', n', m')
  go n m (PReg v (DepType t ts) : bis) =
    let (bis', n', m') = go (n+1) (M.insert v (VarID n) m) bis in
    (VDReg (sortIx M.! t) (S.fromList ((m M.!) <$> ts)) : bis', n', m')

translateTerm :: M.Map Ident SortID -> Ident -> [PBinder] -> DepType -> VTermData
translateTerm sortIx = \x args (DepType t ts) ->
  let (args', n, varIx) = trBinders sortIx args in
  VTermData (Just x) (toVBinder <$> args') $
    VType (sortIx M.! t) ((varIx M.!) <$> ts)

translateAxiom :: M.Map Ident SortID -> M.Map Ident TermID ->
  Ident -> [PBinder] -> [SExpr] -> SExpr -> VAssrtData
translateAxiom sortIx termIx = \x args hs ret ->
  let (args', _, varIx) = trBinders sortIx args in
  VAssrtData (toVBinder <$> args') (makeDV args')
    (trExpr varIx <$> hs) (trExpr varIx ret) where

  trExpr :: M.Map Ident VarID -> SExpr -> VExpr
  trExpr varIx = go where
    go (SVar v) = VVar (varIx M.! v)
    go (App t es) = VApp (termIx M.! t) (go <$> es)

substExpr :: Q.Seq VExpr -> VExpr -> VExpr
substExpr m = go where
  go (VVar (VarID v)) = Q.index m v
  go (VApp t es) = VApp t (go <$> es)

makeDV :: [VDBinder] -> [(VarID, VarID)]
makeDV = go 0 [] where
  go :: Int -> [VarID] -> [VDBinder] -> [(VarID, VarID)]
  go n bs [] = []
  go n bs (VDReg _ ts : bis) =
    ((,) (VarID n) <$> (filter (`S.notMember` ts) bs)) ++ go (n+1) bs bis
  go n bs (VDBound _ : bis) = ((,) (VarID n) <$> bs) ++ go (n+1) (VarID n : bs) bis

type HeapID = Int

data StackSlot =
  -- | A bound variable.
    SSBound SortID VarID
  -- | A term with the given sort. The bit set gives the variables used in the expression.
  | SSExpr SortID VExpr VBitSet
  -- | A proof of a term
  | SSProof VExpr
  deriving (Eq)

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
  vHeap :: Q.Seq StackSlot,
  -- | Recently proven expressions
  vStack :: [StackSlot] }

data LocalCmd =
    Load HeapID
  | PushApp TermID
  | PushThm ThmID
  | Save

type VerifyM = StateT VState (Either String)

verifyProof :: VGlobal -> Q.Seq VDBinder -> [VExpr] -> [LocalCmd] -> Either String VExpr
verifyProof g = \ctx hs cs -> do
  guardError "variable limit exceeded" (ltBitSize (Q.length ctx))
  let heap = Q.foldlWithIndex (\s n b -> s Q.|> varToStackSlot n b) Q.empty ctx
  let heap' = foldl (\s h -> s Q.|> SSProof h) heap hs
  execStateT (mapM_ verify1 cs) (VState heap' []) >>= \case
    VState _ [SSProof e] -> return e
    _ -> throwError "Bad proof state"
  where
  varToStackSlot :: Int -> VDBinder -> StackSlot
  varToStackSlot n (VDBound s) = SSBound s (VarID n)
  varToStackSlot n (VDReg s vs) = SSExpr s (VVar (VarID n))
    (S.foldl' (\bs (VarID v) -> bs .|. bit v) 0 vs)

  push :: StackSlot -> VerifyM ()
  push ss = modify (\(VState heap stk) -> VState heap (ss:stk))

  popn :: [a] -> ([(a, StackSlot)] -> VerifyM c) -> VerifyM c
  popn [] f = f []
  popn (a:as) f = popn as $ \l -> StateT $ \case
    VState heap [] -> throwError "stack underflow"
    VState heap (ss:stk) -> runStateT (f ((a, ss) : l)) (VState heap stk)

  verify1 :: LocalCmd -> VerifyM ()
  verify1 (Load h) = StateT $ \(VState heap stk) -> do
    ss <- fromJustError "index out of bounds" (heap Q.!? h)
    return ((), VState heap (ss:stk))
  verify1 Save = StateT $ \case
    VState heap [] -> throwError "stack underflow"
    VState heap (ss:stk) -> return ((), VState (heap Q.|> ss) (ss:stk))
  verify1 (PushApp t) = do
    VTermData _ args (VType ret _) <- fromJustError "term not found" (vTerms g Q.!? ofTermID t)
    (es, b) <- popn args (verifyArgs 0 (.|.))
    push (SSExpr ret (VApp t es) b)
  verify1 (PushThm t) = do
    VAssrtData args dv hs ret <- fromJustError "theorem not found" (vThms g Q.!? ofThmID t)
    (vs', hs', es, b) <- popn hs $ \hs' -> popn args $ \vs' ->
      do (es, b) <- verifyArgs Q.empty (Q.<|) vs'; return (vs', hs', es, b)
    let subst = Q.fromList es
    guardError "disjoint variable violation" $
      all (\(VarID v1, VarID v2) -> Q.index b v1 .|. Q.index b v2 == 0) dv
    guardError "substitution to hypothesis does not match theorem" $
      all (\(e, ss) -> SSProof (substExpr subst e) == ss) hs'
    push (SSProof (substExpr subst ret))

  verifyArgs :: a -> (VBitSet -> a -> a) -> [(VBinder, StackSlot)] -> VerifyM ([VExpr], a)
  verifyArgs a f = go where
    go [] = return ([], a)
    go ((VBound s', SSBound s v) : sss) = do
      guardError "type mismatch" (s == s')
      (\(l, b) -> (VVar v : l, f (bit (ofVarID v)) b)) <$> go sss
    go ((VBound _, _) : _) = throwError "non-bound variable in BV slot"
    go ((VReg s' _, ss) : sss) = do
      (s, e, b) <- fromJustError "bad stack slot" (ofSSExpr ss)
      guardError "type mismatch" (s == s')
      (\(l, b') -> (e : l, f b b')) <$> go sss
