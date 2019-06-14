module MMTypes where

import Control.Monad.Trans.State
import Data.Maybe
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
data VarStatus = VSBound | VSFree | VSOpen | VSHyp deriving (Eq, Show)
type Frame = ([(VarStatus, Label)], DVs)
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
  | Term Frame (Const, MMExpr) (Maybe ([Label], Proof))
  | Thm Frame (Const, MMExpr) (Maybe ([Label], Proof))
  | Alias Label
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

data MMNatDed = MMNatDed {
  ndProv :: Label,
  ndConj :: Label,
  ndEmpty :: Label,
  ndAssume :: [Label],
  ndWeak :: [Label],
  ndCut :: [Label],
  ndTrue :: Maybe (Label, [Label]),
  ndImp :: Maybe (Label, [Label]),
  ndAnd :: Maybe (Label, [Label]),
  ndOr :: Maybe (Label, [Label]),
  ndNot :: Maybe (Label, Label, [Label]) } deriving (Show)

mkNatDed :: Label -> Label -> Label -> MMNatDed
mkNatDed p c e = MMNatDed p c e [] [] [] Nothing Nothing Nothing Nothing Nothing

data MMMetaData = MMMetaData {
  mPrim :: S.Set Label,
  mEqual :: (M.Map Sort Equality, M.Map Label Sort),
  mNF :: M.Map (Sort, Sort) NF,
  mCondEq :: M.Map Sort (Label, Label),
  mJustification :: M.Map Label Label,
  mCongr :: M.Map Label Label,
  mCCongr :: [Label],
  mND :: Maybe MMNatDed }
  deriving (Show)

mkMetadata :: MMMetaData
mkMetadata = MMMetaData mempty mempty mempty mempty mempty mempty [] Nothing

data MMDatabase = MMDatabase {
  mSorts :: M.Map Sort (Maybe Sort, SortData),
  mDecls :: Q.Seq Decl,
  mMeta :: MMMetaData,
  mStmts :: M.Map Label (Int, Stmt) } deriving (Show)

getStmtM :: MMDatabase -> Label -> Maybe (Int, Stmt)
getStmtM db = go where
  go l = mStmts db M.!? l >>= \case
    (_, Alias s) -> go s
    s -> return s

getStmt :: MMDatabase -> Label -> (Int, Stmt)
getStmt db l = fromJust (getStmtM db l)

mkDatabase :: MMDatabase
mkDatabase = MMDatabase M.empty Q.empty mkMetadata M.empty

vsPure :: VarStatus -> Bool
vsPure VSBound = True
vsPure VSFree = True
vsPure _ = False

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
