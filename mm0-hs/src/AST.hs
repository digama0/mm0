module AST where
import qualified Data.ByteString as B

type Ident = String

type AST = [Stmt]

data Stmt =
    Sort {
      sId :: Ident,
      sPure :: Bool,
      sStrict :: Bool,
      sProvable :: Bool,
      sNonempty :: Bool }
  | Var [Ident] Type
  | Term Ident [Binder] Type
  | Axiom Ident [Binder] Type
  | Theorem Ident [Binder] Type
  | Def Ident [Binder] Type (Maybe Formula)
  | Notation Notation
  | Output OutputKind Ident [Binder]
  | Block [Stmt]
  deriving (Show)

data Notation =
    Prefix Ident Const Prec
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
  | TOpenType Ident
  | TFormula Formula
  deriving (Show)

type Formula = B.ByteString

data Binder = Binder Local Type deriving (Show)
