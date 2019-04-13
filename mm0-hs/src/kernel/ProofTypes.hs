module ProofTypes where

import Debug.Trace
import Data.Bits
import Data.Maybe
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Q
import Environment (Ident)

newtype SortID = SortID {ofSortID :: Int} deriving (Eq)
newtype TermID = TermID {ofTermID :: Int} deriving (Eq, Ord)
newtype ThmID = ThmID {ofThmID :: Int}
newtype VarID = VarID {ofVarID :: Int} deriving (Eq, Ord)

instance Show SortID where show (SortID n) = "s" ++ show n
instance Show TermID where show (TermID n) = "t" ++ show n
instance Show ThmID where show (ThmID n) = "T" ++ show n
instance Show VarID where show (VarID n) = "v" ++ show n

data VType = VType SortID [VarID]
data VBinder = VBound SortID | VReg SortID [VarID] deriving (Eq)
data VExpr = VVar VarID | VApp TermID [VExpr] deriving (Eq)

class IDPrinter a where
  ppSort :: a -> SortID -> Ident
  ppTerm :: a -> TermID -> Ident
  ppThm :: a -> ThmID -> Ident
  ppVar :: a -> VarID -> Ident
  ppInsertSort :: Ident -> a -> a
  ppInsertTerm :: Maybe Ident -> a -> a
  ppInsertThm :: Maybe Ident -> a -> a
  ppInsertVar :: Ident -> a -> a

instance IDPrinter () where
  ppSort _ = show
  ppTerm _ = show
  ppThm _ = show
  ppVar _ = show
  ppInsertSort _ = id
  ppInsertTerm _ = id
  ppInsertThm _ = id
  ppInsertVar _ = id

data SeqPrinter = SeqPrinter {
  mpSorts :: Q.Seq Ident,
  mpTerms :: Q.Seq Ident,
  mpThms :: Q.Seq Ident,
  mpVars :: Q.Seq Ident }

mkSeqPrinter :: SeqPrinter
mkSeqPrinter = SeqPrinter Q.empty Q.empty Q.empty Q.empty

instance IDPrinter SeqPrinter where
  ppSort m n = fromMaybe (show 42) (mpSorts m Q.!? ofSortID n)
  ppTerm m n = fromMaybe (show n) (mpTerms m Q.!? ofTermID n)
  ppThm m n = fromMaybe (show n) (mpThms m Q.!? ofThmID n)
  ppVar m n = fromMaybe (show n) (mpVars m Q.!? ofVarID n)
  ppInsertSort x m = m {mpSorts = traceShowId (mpSorts m Q.|> x)}
  ppInsertTerm x m = m {mpTerms = mpTerms m Q.|>
    fromMaybe (show (TermID (Q.length (mpTerms m)))) x}
  ppInsertThm x m = m {mpThms = mpThms m Q.|>
    fromMaybe (show (ThmID (Q.length (mpThms m)))) x}
  ppInsertVar x m = m {mpVars = mpVars m Q.|> x}

ppType :: IDPrinter a => a -> VType -> ShowS
ppType a (VType s vs) =
  (ppSort a s ++) . flip (foldr (\v -> (' ' :) . (ppVar a v ++))) vs

instance Show VType where showsPrec _ = ppType ()

ppBinder :: IDPrinter a => a -> VarID -> VBinder -> ShowS
ppBinder a v (VBound s) r = '{' : ppVar a v ++ ": " ++ ppSort a s ++ '}' : r
ppBinder a v (VReg s vs) r = '(' : ppVar a v ++ ": " ++ ppType a (VType s vs) (')' : r)

ppBinders :: IDPrinter a => a -> [VBinder] -> Int -> (ShowS, Int)
ppBinders a [] n = (id, n)
ppBinders a (b : bs) n =
  let (s, n') = ppBinders a bs (n+1) in
  ((' ' :) . ppBinder a (VarID n) b . s, n')

ppExpr :: IDPrinter a => a -> Int -> VExpr -> ShowS
ppExpr a n (VVar v) r = ppVar a v ++ r
ppExpr a n (VApp t []) r = ppTerm a t ++ r
ppExpr a n (VApp t es) r =
  let f r = ppTerm a t ++ foldr (\e r -> ' ' : ppExpr a 1 e r) r es in
  if n == 0 then f r else '(' : f (')' : r)

instance Show VExpr where showsPrec = ppExpr ()

ppHyps :: IDPrinter a => a -> [VExpr] -> Int -> (ShowS, Int)
ppHyps a [] n = (id, n)
ppHyps a (h : hs) n =
  let (s, n') = ppHyps a hs (n+1) in
  (\r -> "\n  (" ++ ppVar a (VarID n) ++ ": " ++ ppExpr a 1 h (')' : s r), n')

isBound :: VBinder -> Bool
isBound (VBound _) = True
isBound _ = False

data VInoutKind = VIKString Bool deriving (Show)

type Proofs = [ProofCmd]
data ProofCmd =
    StepSort Ident
  | StepTerm Ident
  | StepAxiom Ident
  | ProofDef {
      pdName :: Maybe Ident,  -- ^ The name of the definition
      pdArgs :: [VBinder],    -- ^ The arguments to the definition
      pdRet :: VType,         -- ^ The return type
      pdDummies :: [SortID],  -- ^ The types of the dummies
      pdVal :: VExpr,         -- ^ The value of the definition
      pdStep :: Bool }        -- ^ True if this def is in the spec
  | ProofThm {
      ptName :: Maybe Ident, -- ^ The name of the theorem
      ptVar :: [VBinder],    -- ^ The variables
      ptHyps :: [VExpr],     -- ^ The hypotheses
      ptRet :: VExpr,        -- ^ The return type
      ptUnfold :: [TermID],  -- ^ Which definitions to unfold in the statement
      ptDummies :: [SortID], -- ^ The types of the dummies
      ptProof :: ProofTree,  -- ^ The actual proof
      ptStep :: Bool }       -- ^ True if this theorem is in the spec
  | StepInout VInoutKind

ppProofCmd' :: IDPrinter a => a -> ProofCmd -> (ShowS, a)
ppProofCmd' a (StepSort x) = (("sort " ++) . (x ++), ppInsertSort x a)
ppProofCmd' a (StepTerm x) = (("term " ++) . (x ++), ppInsertTerm (Just x) a)
ppProofCmd' a (StepAxiom x) = (("axiom " ++) . (x ++), ppInsertThm (Just x) a)
ppProofCmd' a (ProofDef x args ret ds val st) =
  let (sargs, n) = ppBinders a args 0
      (sds, _) = ppBinders a (VBound <$> ds) n in
  ((((if st then "" else "local ") ++ "def " ++ fromMaybe "_" x) ++) .
    sargs . (": " ++) . ppType a ret . (" =\n" ++) . sds . (' ' :) . ppExpr a 1 val,
  ppInsertTerm x a)
ppProofCmd' a (ProofThm x args hs ret uf ds pf st) =
  let (sargs, n) = ppBinders a args 0
      (shs, n2) = ppHyps a hs n
      (sds, n3) = ppBinders a (VBound <$> ds) n2
      suf r = case uf of
        [] -> r
        u:us -> " unfolding(" ++ ppTerm a u ++
          foldr (\u' r -> ' ' : ppTerm a u' ++ r) (')' : r) us in
  (\r -> (if st then "" else "local ") ++ "theorem " ++ fromMaybe "_" x ++
    sargs ((',' :) $ suf $ sds $ shs $ (": " ++) $
      ppExpr a 1 ret $ " =\n" ++ fst (ppProofTree a pf n3) r),
  ppInsertThm x a)

ppProofCmd :: IDPrinter a => a -> ProofCmd -> ShowS
ppProofCmd a c = fst (ppProofCmd' a c)

instance Show ProofCmd where showsPrec _ = ppProofCmd ()

type HeapID = VarID

data ProofTree =
    Load HeapID
  | VTerm TermID [ProofTree]
  | VThm ThmID [ProofTree]
  | Save ProofTree
  | Sorry
  deriving (Show)

exprToPT :: VExpr -> ProofTree
exprToPT (VVar v) = Load v
exprToPT (VApp t es) = VTerm t (map exprToPT es)

ppProofTree :: IDPrinter a => a -> ProofTree -> Int -> (ShowS, Int)
ppProofTree a (Load h) n = ((ppVar a h ++), n)
ppProofTree a (VTerm t es) n =
  let (s, n') = foldl (\(s1, n1) t' ->
        let (s2, n2) = ppProofTree a t' n1 in
        (s1 . (' ' :) . s2, n2)) (id, n) es in
  (\r -> '(' : ppTerm a t ++ s (')' : r), n')
ppProofTree a (VThm t es) n =
  let (s, n') = foldl (\(s1, n1) t' ->
        let (s2, n2) = ppProofTree a t' n1 in
        (s1 . (' ' :) . s2, n2)) (id, n) es in
  (\r -> '(' : ppThm a t ++ s (')' : r), n')
ppProofTree a (Save p) n =
  let (s, n') = ppProofTree a p n in
  (\r -> '[' : s ('=' : ppVar a (VarID n') ++ ']' : r), n' + 1)
ppProofTree a Sorry n = (('?' :), n)

type NameMap = (Int, M.Map Ident Int)

nempty :: NameMap
nempty = (0, M.empty)

ninsert :: Ident -> NameMap -> NameMap
ninsert v (n, m) = (n+1, M.insert v n m)

data IxLookup = IxLookup {
  -- | Map from sort to SortID
  pSortIx :: NameMap,
  -- | Map from term to TermID
  pTermIx :: NameMap,
  -- | Map from theorem to ThmID
  pThmIx :: NameMap,
  -- | Map from var to VarID
  pVarIx :: NameMap }

mkIxLookup :: IxLookup
mkIxLookup = IxLookup nempty nempty nempty nempty

ilInsertSort :: Ident -> IxLookup -> IxLookup
ilInsertSort i s = s {pSortIx = ninsert i (pSortIx s)}

ilInsertTerm :: Ident -> IxLookup -> IxLookup
ilInsertTerm i s = s {pTermIx = ninsert i (pTermIx s)}

ilInsertThm :: Ident -> IxLookup -> IxLookup
ilInsertThm i s = s {pThmIx = ninsert i (pThmIx s)}

ilInsertVar :: Ident -> IxLookup -> IxLookup
ilInsertVar i s = s {pVarIx = ninsert i (pVarIx s)}

ilResetVars :: IxLookup -> IxLookup
ilResetVars s = s {pVarIx = (0, M.empty)}

ilSort :: IxLookup -> Ident -> Maybe SortID
ilSort s i = SortID <$> snd (pSortIx s) M.!? i

ilTerm :: IxLookup -> Ident -> Maybe TermID
ilTerm s i = TermID <$> snd (pTermIx s) M.!? i

ilThm :: IxLookup -> Ident -> Maybe ThmID
ilThm s i = ThmID <$> snd (pThmIx s) M.!? i

ilVar :: IxLookup -> Ident -> Maybe VarID
ilVar s i = VarID <$> snd (pVarIx s) M.!? i
