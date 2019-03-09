module AST where
import qualified Data.ByteString as B

type Ident = String

data SortData = SortData {
  sPure :: Bool,
  sStrict :: Bool,
  sProvable :: Bool,
  sNonempty :: Bool }
  deriving (Show)

type AST = [Stmt]

data Stmt = Sort Ident SortData
  | Var [Ident] VarType
  | Term Ident [Binder] Type
  | Axiom Ident [Binder] Type
  | Theorem Ident [Binder] Type
  | Def Ident [Binder] Type (Maybe Formula)
  | Notation Notation
  | Output OutputKind Ident [Binder]
  | Block [Stmt]
  deriving (Show)

data Notation =
    Delimiter Const
  | Prefix Ident Const Prec
  | Infix Bool Ident Const Prec
  | Coercion Ident Ident Ident
  | NNotation Ident [Binder] Type [Literal]
  deriving (Show)

data Literal = NConst Const | NVar Ident Prec deriving (Show)

type Const = B.ByteString
type Prec = Int
type OutputKind = String

data Local = LReg Ident | LDummy Ident | LAnon deriving (Show)

data Type =
    TType Ident [Ident]
  | TFormula Formula
  deriving (Show)

data VarType = VType Ident | Open Ident deriving (Show)

type Formula = B.ByteString

data Binder = Binder Local Type deriving (Show)
