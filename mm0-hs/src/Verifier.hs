module Verifier() where

import Control.Monad.Except
import Control.Monad.Trans.State
import Data.Word
import Data.List
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

type VBitSet = Word64

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

data StackSlot =
  -- | A term with the given sort. The bit set gives the variables used in the expression.
    SSExpr SortID VExpr VBitSet
  -- | A proof of a term
  | SSProof VExpr

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
      ptDummies :: [SortID],    -- ^ The types of the dummies
      ptHyps :: [VExpr],        -- ^ The hypotheses
      ptRet :: VExpr,           -- ^ The return type
      ptUnfold :: Maybe TermID, -- ^ Which definition to unfold in the statement
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
        SDecl x' (DDef args ty o) | x == x' ->
          guardError ("def '" ++ x ++ "' does not match declaration") $
            matchDef (vTermIx g) (vSortIx g) vs ret ds args ty def o
        _ -> throwError "incorrect def step"

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
    (ret', rs') <- typecheckDef (vTerms g) ctx' def
    guardError "type error" (ret == ret')
    guardError "unaccounted free variables" (S.isSubsetOf rs' (S.fromList rs))

  typecheckDef :: Q.Seq VTermData -> Q.Seq VDBinder -> VExpr -> Either String (SortID, S.Set VarID)
  typecheckDef terms ctx = typecheckExpr where
    typecheckExpr (VVar v) = case ctx Q.!? ofVarID v of
      Nothing -> throwError "undeclared variable in def expr"
      Just (VDBound s) -> return (s, S.singleton v)
      Just (VDReg s vs) -> return (s, vs)
    typecheckExpr (VApp t es) = do
      VTermData _ args (VType ret rs) <- fromJustError "unknown term in def expr" (terms Q.!? ofTermID t)
      (m, ev) <- typecheckArgs args es
      return (ret, ev <> S.fromList ((\v -> m I.! ofVarID v) <$> rs))

    typecheckArgs :: [VBinder] -> [VExpr] -> Either String (I.IntMap VarID, S.Set VarID)
    typecheckArgs args es = go args es 0 I.empty S.empty where
      go [] [] _ m ev = return (m, ev)
      go (VBound s : args) (VVar v : es) n m ev = case ctx Q.!? ofVarID v of
        Just (VDBound s') | s == s' ->
          go args es (n+1) (I.insert n v m) ev
        _ -> throwError "non-bound variable in BV slot"
      go (VBound _ : args) (_ : es) _ _ _ =
        throwError "non-bound variable in BV slot"
      go (VReg s vs : args) (e : es) n m ev = do
        (s', ev') <- typecheckExpr e
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

  matchExpr :: M.Map Ident TermID -> M.Map Ident VarID -> VExpr -> SExpr -> Bool
  matchExpr termIx varIx = matchExpr1 where
    matchExpr1 :: VExpr -> SExpr -> Bool
    matchExpr1 (VVar v) (SVar x) = varIx M.! x == v
    matchExpr1 (VApp t es) (App x ss) = termIx M.! x == t && matchExprs es ss
    matchExpr1 _ _ = False
    matchExprs :: [VExpr] -> [SExpr] -> Bool
    matchExprs [] [] = True
    matchExprs (e:es) (s:ss) = matchExpr1 e s && matchExprs es ss
    matchExprs _ _ = False

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

makeDV :: [VDBinder] -> [(VarID, VarID)]
makeDV = go 0 [] where
  go :: Int -> [VarID] -> [VDBinder] -> [(VarID, VarID)]
  go n bs [] = []
  go n bs (VDReg _ ts : bis) =
    ((,) (VarID n) <$> (filter (`S.notMember` ts) bs)) ++ go (n+1) bs bis
  go n bs (VDBound _ : bis) = ((,) (VarID n) <$> bs) ++ go (n+1) (VarID n : bs) bis

type HeapID = Int

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

runVerifyM :: VerifyM a -> Either String (a, VExpr)
runVerifyM m = do
  runStateT m (VState Q.empty []) >>= \case
    (a, VState _ [SSProof e]) -> return (a, e)
    _ -> throwError "Bad proof state"

verifyProof :: VGlobal -> LocalCmd -> VerifyM ()
verifyProof g = undefined
