module MMTypes where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Sequence as Q

type Const = String
type Var = String
data Sym = Const Const | Var Var deriving (Show)

data Hyp = VHyp Const Var | EHyp [Sym] deriving (Show)

type DVs = S.Set (Var, Var)
type Frame = ([String], DVs)
type Fmla = [Sym]
type Proof = [String]

data Stmt = Hyp Hyp | Thm Frame Fmla Proof deriving (Show)

type Scope = [([(String, Hyp)], [[Var]])]

data MMDatabase = MMDatabase {
  mSorts :: Q.Seq (String, Maybe String),
  mDecls :: Q.Seq String,
  mPrim :: S.Set String,
  mSyms :: M.Map String Sym,
  mStmts :: M.Map String Stmt,
  mScope :: Scope } deriving (Show)
