module Verifier() where

import Control.Monad.Except
import Control.Monad.Trans.State
import Data.Word
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Q
import qualified Data.IntMap as I
import AST (SortData(..), Ident, DepType(..))
import Environment
import Util

type SortID = Int
type TermID = Int
type ThmID = Int
type VarID = Int

data VBinder = VBound SortID | VReg SortID
data VExpr = VVar VarID | VApp TermID [VExpr] deriving (Eq)

type VBitSet = Word64

data VTermData = VTermData {
  vtName :: Maybe Ident, -- ^ Name from the spec
  vtArgs :: [VBinder],   -- ^ Arguments
  vtRet :: SortID }      -- ^ Return value sort

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
  vSortIx :: M.Map Ident Int,
  -- | Map from TermID to term/def info (for constructing expressions)
  vTerms :: Q.Seq VTermData,
  -- | Map from term to TermID
  vTermIx :: M.Map Ident Int,
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

data VType = VType SortID [VarID]

type Proofs = [ProofCmd]
data ProofCmd =
    StepSort Ident
  | StepTerm Ident
  | StepAxiom Ident
  | ProofDef {
      pdArgs :: [VBinder],    -- ^ The arguments to the definition
      pdRet :: VType,         -- ^ The return type
      pdDummies :: [SortID],  -- ^ The types of the dummies
      pdVal :: VExpr,         -- ^ The value of the definition
      pdStep :: Maybe Ident } -- ^ The name of the definition in the spec
  | ProofThm {
      ptVar :: [VBinder],         -- ^ The variables
      ptDummies :: [SortID],      -- ^ The types of the dummies
      ptHyps :: [VExpr],          -- ^ The hypotheses
      ptRet :: VExpr,             -- ^ The return type
      ptUnfold :: TermID -> Bool, -- ^ Which definitions to unfold in the statement
      ptProof :: [LocalCmd],      -- ^ The actual proof
      ptStep :: Maybe Ident }     -- ^ The name of the theorem in the spec

verify :: Environment -> Proofs -> Either String ()
verify env = \p -> runGVerifyM (mapM_ verifyCmd p) env where

  verifyCmd :: ProofCmd -> GVerifyM ()
  verifyCmd (StepSort x) = step >>= \case
    SSort x' sd | x == x' -> modify (\g -> g {
      vSorts = vSorts g Q.|> (x, sd),
      vSortIx = M.insert x (Q.length (vSorts g)) (vSortIx g) })
    _ -> throwError "incorrect sort step"
  verifyCmd (StepTerm x) = step >>= \case
    SDecl x' (DTerm args ty) | x == x' -> modify (\g -> g {
      vTerms = vTerms g Q.|> translateTerm (vSortIx g) x args ty,
      vTermIx = M.insert x (Q.length (vTerms g)) (vTermIx g) })
    _ -> throwError "incorrect term step"
  verifyCmd (StepAxiom x) = step >>= \case
    SDecl x' (DAxiom args hs ret) | x == x' -> modify (\g -> g {
      vThms = vThms g Q.|> translateAxiom (vSortIx g) (vTermIx g) x args hs ret })
    _ -> throwError "incorrect axiom step"

  step :: GVerifyM Spec
  step = do
    n <- vPos <$> get
    fromJustError "nothing more to prove" (eSpec env Q.!? n)

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

translateTerm :: M.Map Ident Int -> Ident -> [PBinder] -> DepType -> VTermData
translateTerm sortIx = \x bs (DepType t _) ->
  VTermData (Just x) (trBinder <$> bs) (sortIx M.! t) where
  trBinder :: PBinder -> VBinder
  trBinder (PBound _ t) = VBound (sortIx M.! t)
  trBinder (PReg _ (DepType t _)) = VReg (sortIx M.! t)

translateAxiom :: M.Map Ident SortID -> M.Map Ident TermID ->
  Ident -> [PBinder] -> [SExpr] -> SExpr -> VAssrtData
translateAxiom sortIx termIx = \x args hs ret ->
  case trBinders args 0 M.empty of
    (args', bs, varIx) ->
      VAssrtData args' (makeDV varIx args bs)
        (trExpr varIx <$> hs) (trExpr varIx ret)
  where

  trBinders :: [PBinder] -> VarID -> M.Map Ident VarID -> ([VBinder], [VarID], M.Map Ident VarID)
  trBinders (PBound v t : bis) n m =
    case trBinders bis (n+1) (M.insert v n m) of
      (bis', bs, m') -> (VBound (sortIx M.! t) : bis', n : bs, m')
  trBinders (PReg v (DepType t _) : bis) n m =
    case trBinders bis (n+1) (M.insert v n m) of
      (bis', bs, m') -> (VReg (sortIx M.! t) : bis', bs, m')

  trExpr :: M.Map Ident VarID -> SExpr -> VExpr
  trExpr varIx = go where
    go (SVar v) = VVar (varIx M.! v)
    go (App t es) = VApp (termIx M.! t) (go <$> es)

makeDV :: M.Map Ident VarID -> [PBinder] -> [VarID] -> [(VarID, VarID)]
makeDV varIx bis bs = makeDV1 bs where

  makeDV1 :: [VarID] -> [(VarID, VarID)]
  makeDV1 [] = makeDV2 bis 0
  makeDV1 (b:bs) = ((,) b <$> bs) ++ makeDV1 bs

  makeDV2 :: [PBinder] -> Int -> [(VarID, VarID)]
  makeDV2 [] n = []
  makeDV2 (PReg _ (DepType _ ts) : bis) n =
    ((\v -> (n, varIx M.! v)) <$> ts) ++ makeDV2 bis (n+1)
  makeDV2 (_ : bis) n = makeDV2 bis (n+1)
