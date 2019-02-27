module Types where
import qualified Data.ByteString.Lazy as B

type Ident = String

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
  | Def Ident [Binder] Type Formula [Stmt]
  | Notation Notation
  | Output OutputKind Ident [Binder]
  | Block [Stmt]

data Notation =
    Prefix Ident Const Prec
  | Infix Bool Ident Const Prec
  | Coercion Ident Ident Ident
  | NNotation Ident [Binder] Type [Literal]

data Literal = NConst Const | NVar Ident Prec

type Const = B.ByteString
type Prec = Int
type OutputKind = String

data Local = LReg Ident | LDummy Ident | LAnon

data Type =
    TType Ident [Ident]
  | TOpenType Ident
  | TFormula Formula

type Formula = B.ByteString

data Binder = Binder Local Type
