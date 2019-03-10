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

data Literal = NConst Const Prec | NVar Ident deriving (Show)

type Const = B.ByteString
type Prec = Int
type OutputKind = String

data Local = LReg Ident | LDummy Ident | LAnon

instance Show Local where
  showsPrec _ (LReg v) r = v ++ r
  showsPrec _ (LDummy v) r = '.' : v ++ r
  showsPrec _ LAnon r = '_' : r

data Type =
    TType Ident [Ident]
  | TFormula Formula
  deriving (Show)

data VarType = VType Ident | Open Ident

instance Show VarType where
  showsPrec _ (VType v) r = v ++ r
  showsPrec _ (Open v) r = v ++ '*' : r

type Formula = B.ByteString

data Binder = Binder Local Type

instance Show Binder where
  showsPrec n (Binder l ty) = showsPrec n l . (": " ++) . showsPrec n ty

localName :: Local -> Maybe Ident
localName (LReg v) = Just v
localName (LDummy v) = Just v
localName LAnon = Nothing

varTypeSort :: VarType -> Ident
varTypeSort (VType s) = s
varTypeSort (Open s) = s
