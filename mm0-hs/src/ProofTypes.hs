module ProofTypes where

import Data.Bits
import AST

newtype SortID = SortID {ofSortID :: Int} deriving (Eq)
newtype TermID = TermID {ofTermID :: Int} deriving (Eq)
newtype ThmID = ThmID {ofThmID :: Int}
newtype VarID = VarID {ofVarID :: Int} deriving (Eq, Ord)

data VType = VType SortID [VarID]
data VBinder = VBound SortID | VReg SortID [VarID] deriving (Eq)
data VExpr = VVar VarID | VApp TermID [VExpr] deriving (Eq)

isBound :: VBinder -> Bool
isBound (VBound _) = True
isBound _ = False

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
      ptVar :: [VBinder],       -- ^ The variables
      ptHyps :: [VExpr],        -- ^ The hypotheses
      ptRet :: VExpr,           -- ^ The return type
      ptUnfold :: Maybe TermID, -- ^ Which definition to unfold in the statement
      ptDummies :: [SortID],    -- ^ The types of the dummies
      ptProof :: [LocalCmd],    -- ^ The actual proof
      ptStep :: Maybe Ident }   -- ^ The name of the theorem in the spec

type HeapID = Int

data LocalCmd =
    Load HeapID
  | PushApp TermID
  | PushThm ThmID
  | Save
