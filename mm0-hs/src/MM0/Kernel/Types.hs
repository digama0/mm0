module MM0.Kernel.Types where

import MM0.Kernel.Environment

data VInoutKind = VIKString Bool deriving (Show)

data Stmt =
    StepSort Ident
  | StepTerm Ident
  | StepAxiom Ident
  | StmtDef {
      pdName :: TermName,     -- ^ The name of the definition
      pdArgs :: [PBinder],    -- ^ The arguments to the definition
      pdRet :: DepType,       -- ^ The return type
      pdDummies :: [(VarName, Sort)], -- ^ The types of the dummies
      pdVal :: SExpr,         -- ^ The value of the definition
      pdStep :: Bool }        -- ^ True if this def is in the spec
  | StmtThm {
      ptName :: ThmName,     -- ^ The name of the theorem
      ptVar :: [PBinder],    -- ^ The variables
      ptHyps :: [(VarName, SExpr)], -- ^ The hypotheses
      ptRet :: SExpr,        -- ^ The return type
      ptDummies :: [(VarName, Sort)], -- ^ The dummies
      ptProof :: Proof,      -- ^ The actual proof
      ptStep :: Bool }       -- ^ True if this theorem is in the spec
  | StepInout VInoutKind
  deriving (Show)

data Proof =
    PHyp VarName
  | PThm ThmName [SExpr] [Proof]
  | PConv SExpr Conv Proof
  | PLet VarName Proof Proof
  | PSorry
  deriving (Show)

data Conv =
    CVar VarName
  | CApp TermName [Conv]
  | CSym Conv
  | CUnfold TermName [SExpr] [VarName] Conv
  deriving (Show)
