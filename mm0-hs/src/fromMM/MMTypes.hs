module MMTypes where

import Control.Monad.Trans.State
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Sequence as Q
import Environment (SortData, SExpr)

type Const = String
type Var = String
type Sort = String
type Label = String
type MMExpr = SExpr

data Hyp = VHyp Const Var | EHyp Const MMExpr deriving (Show)

type DVs = S.Set (Label, Label)
type Frame = ([(Bool, Label)], DVs)
data Proof =
    PHyp Label Int
  | PDummy Int
  | PBackref Int
  | PSorry
  | PSave Proof
  | PTerm Label [Proof]
  | PThm Label [Proof]
  deriving (Show)

data Stmt = Hyp Hyp
  | Term Frame Const MMExpr (Maybe ([Label], Proof))
  | Thm Frame Const MMExpr (Maybe ([Label], Proof))
  deriving (Show)

data Decl = Sort Sort | Stmt Label deriving (Show)

data Equality = Equality {
  eEq :: Label,
  eRefl :: Label,
  eSymm :: Label,
  eTrans :: Label } deriving (Show)

data NF = NF {
  nfNF :: Label,
  nfCond :: Label } deriving (Show)

data MMMetaData = MMMetaData {
  mPrim :: S.Set Label,
  mEqual :: M.Map Sort Equality,
  mNF :: M.Map (Sort, Sort) NF,
  mCondEq :: M.Map Sort (Label, Label),
  mJustification :: M.Map Label Label,
  mCongr :: M.Map Label Label,
  mCCongr :: [Label] }
  deriving (Show)

mkMetadata :: MMMetaData
mkMetadata = MMMetaData S.empty M.empty M.empty M.empty M.empty M.empty []

data MMDatabase = MMDatabase {
  mSorts :: M.Map Sort (Maybe Sort, SortData),
  mDecls :: Q.Seq Decl,
  mMeta :: MMMetaData,
  mStmts :: M.Map Label Stmt } deriving (Show)

mkDatabase :: MMDatabase
mkDatabase = MMDatabase M.empty Q.empty mkMetadata M.empty

orientPair :: Ord a => (a, a) -> (a, a)
orientPair (a1, a2) = if a1 < a2 then (a1, a2) else (a2, a1)

memDVs :: DVs -> Label -> Label -> Bool
memDVs d v1 v2 = S.member (orientPair (v1, v2)) d

unsave :: Proof -> (Proof, Q.Seq Proof)
unsave = \p -> runState (go p) Q.empty where
  go :: Proof -> State (Q.Seq Proof) Proof
  go (PTerm t ps) = PTerm t <$> mapM go ps
  go (PThm t ps) = PThm t <$> mapM go ps
  go (PSave p) = do
    p' <- go p
    state $ \heap -> (PBackref (Q.length heap), heap Q.|> p')
  go p = return p
