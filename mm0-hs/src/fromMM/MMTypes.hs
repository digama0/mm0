module MMTypes where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Sequence as Q
import Environment (SortData)

type Const = String
type Var = String
type Sort = String
type Label = String
data Sym = Const Const | Var Var deriving (Show)

data Hyp = VHyp Const Var | EHyp [Sym] deriving (Show)

type DVs = S.Set (Var, Var)
type Frame = ([Label], DVs)
type Fmla = [Sym]
type Proof = [String]

data Stmt = Hyp Hyp | Thm Frame Fmla Proof deriving (Show)

type Scope = [([(Label, Hyp)], [[Var]], S.Set Var)]

data Decl = Sort Sort | Stmt Label deriving (Show)

data MMDatabase = MMDatabase {
  mSorts :: M.Map Sort (Maybe Sort, SortData),
  mDecls :: Q.Seq Decl,
  mPrim :: S.Set Label,
  mSyms :: M.Map String Sym,
  mStmts :: M.Map Label Stmt,
  mScope :: Scope } deriving (Show)

memDVs :: DVs -> Var -> Var -> Bool
memDVs d v1 v2 = S.member (if v1 < v2 then (v1, v2) else (v2, v1)) d
