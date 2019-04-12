module ProofTypes where

import Data.Bits
import qualified Data.Map.Strict as M
import Environment (Ident)

newtype SortID = SortID {ofSortID :: Int} deriving (Eq)
newtype TermID = TermID {ofTermID :: Int} deriving (Eq, Ord)
newtype ThmID = ThmID {ofThmID :: Int}
newtype VarID = VarID {ofVarID :: Int} deriving (Eq, Ord)

instance Show SortID where show (SortID n) = "s" ++ show n
instance Show TermID where show (TermID n) = "t" ++ show n
instance Show ThmID where show (ThmID n) = "T" ++ show n
instance Show VarID where show (VarID n) = "v" ++ show n

data VType = VType SortID [VarID] deriving (Show)
data VBinder = VBound SortID | VReg SortID [VarID] deriving (Show, Eq)
data VExpr = VVar VarID | VApp TermID [VExpr] deriving (Eq)

instance Show VExpr where
  showsPrec n (VVar v) r = showsPrec n v r
  showsPrec n (VApp v []) r = showsPrec n v r
  showsPrec n (VApp v vs) r =
    let f r = showsPrec 0 v (foldr (\e r -> ' ' : showsPrec 1 e r) r vs) in
    if n == 0 then f r else '(' : f (')' : r)

isBound :: VBinder -> Bool
isBound (VBound _) = True
isBound _ = False

data VInoutKind = VIKString Bool deriving (Show)

type Proofs = [ProofCmd]
data ProofCmd =
    StepSort Ident
  | StepTerm Ident
  | StepAxiom Ident
  | ProofDef {
      pdName :: Maybe Ident,  -- ^ The name of the definition
      pdArgs :: [VBinder],    -- ^ The arguments to the definition
      pdRet :: VType,         -- ^ The return type
      pdDummies :: [SortID],  -- ^ The types of the dummies
      pdVal :: VExpr,         -- ^ The value of the definition
      pdStep :: Bool }        -- ^ True if this def is in the spec
  | ProofThm {
      ptName :: Maybe Ident, -- ^ The name of the theorem
      ptVar :: [VBinder],    -- ^ The variables
      ptHyps :: [VExpr],     -- ^ The hypotheses
      ptRet :: VExpr,        -- ^ The return type
      ptUnfold :: [TermID],  -- ^ Which definition to unfold in the statement
      ptDummies :: [SortID], -- ^ The types of the dummies
      ptProof :: [LocalCmd], -- ^ The actual proof
      ptStep :: Bool }       -- ^ True if this theorem is in the spec
  | StepInout VInoutKind
  deriving (Show)

type HeapID = Int

data LocalCmd =
    Load HeapID
  | PushApp TermID
  | PushThm ThmID
  | Save
  | Sorry
  deriving (Show)

type NameMap = (Int, M.Map Ident Int)

nempty :: NameMap
nempty = (0, M.empty)

ninsert :: Ident -> NameMap -> NameMap
ninsert v (n, m) = (n+1, M.insert v n m)

data IxLookup = IxLookup {
  -- | Map from sort to SortID
  pSortIx :: NameMap,
  -- | Map from term to TermID
  pTermIx :: NameMap,
  -- | Map from theorem to ThmID
  pThmIx :: NameMap,
  -- | Map from var to VarID
  pVarIx :: NameMap }

mkIxLookup :: IxLookup
mkIxLookup = IxLookup nempty nempty nempty nempty

ilInsertSort :: Ident -> IxLookup -> IxLookup
ilInsertSort i s = s {pSortIx = ninsert i (pSortIx s)}

ilInsertTerm :: Ident -> IxLookup -> IxLookup
ilInsertTerm i s = s {pTermIx = ninsert i (pTermIx s)}

ilInsertThm :: Ident -> IxLookup -> IxLookup
ilInsertThm i s = s {pThmIx = ninsert i (pThmIx s)}

ilInsertVar :: Ident -> IxLookup -> IxLookup
ilInsertVar i s = s {pVarIx = ninsert i (pVarIx s)}

ilResetVars :: IxLookup -> IxLookup
ilResetVars s = s {pVarIx = (0, M.empty)}

ilSort :: IxLookup -> Ident -> Maybe SortID
ilSort s i = SortID <$> snd (pSortIx s) M.!? i

ilTerm :: IxLookup -> Ident -> Maybe TermID
ilTerm s i = TermID <$> snd (pTermIx s) M.!? i

ilThm :: IxLookup -> Ident -> Maybe ThmID
ilThm s i = ThmID <$> snd (pThmIx s) M.!? i

ilVar :: IxLookup -> Ident -> Maybe VarID
ilVar s i = VarID <$> snd (pVarIx s) M.!? i
