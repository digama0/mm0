module MM0.Kernel.Types (VInoutKind(..), Stmt(..), Proof(..), Conv(..)) where

import qualified Data.Text as T
import Data.Void
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String
import MM0.Kernel.Environment

data VInoutKind = VIKString Bool -- ^ False for input, True for output
  deriving (Show)

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

data Proof =
    PHyp VarName
  | PThm ThmName [SExpr] [Proof]
  | PConv SExpr Conv Proof
  | PLet VarName Proof Proof
  | PSorry

data Conv =
    CVar VarName
  | CApp TermName [Conv]
  | CSym Conv
  | CUnfold TermName [SExpr] [VarName] Conv

data LispPP = LPAtom T.Text | LPList [LispPP] | LPLarge LispPP

sExprToLP :: SExpr -> LispPP
sExprToLP (SVar v) = LPAtom v
sExprToLP (App t ts) = LPList (LPAtom t : (sExprToLP <$> ts))

convToLP :: Conv -> LispPP
convToLP (CVar v) = LPAtom v
convToLP (CApp t ts) = LPList (LPAtom t : (convToLP <$> ts))
convToLP (CSym c) = LPList [LPAtom ":sym", convToLP c]
convToLP (CUnfold t es vs c) =
  LPList [LPAtom ":unfold", LPAtom t,
    LPList (sExprToLP <$> es), LPList (LPAtom <$> vs), convToLP c]

proofToLP :: Proof -> LispPP
proofToLP (PHyp h) = LPAtom h
proofToLP (PThm t es ps) =
  LPList (LPAtom t : LPList (sExprToLP <$> es) : (LPLarge . proofToLP <$> ps))
proofToLP (PConv t c p) =
  LPList [LPAtom ":conv", sExprToLP t, LPLarge $ convToLP c, LPLarge $ proofToLP p]
proofToLP (PLet h p q) =
  LPList [LPAtom ":let", LPAtom h, proofToLP p, LPLarge $ proofToLP q]
proofToLP PSorry = LPAtom ":sorry"

depTypeToLP :: DepType -> [LispPP]
depTypeToLP (DepType s vs) = [LPAtom s, LPList (LPAtom <$> vs)]

binderToLP :: PBinder -> LispPP
binderToLP (PBound x s) = LPList [LPAtom x, LPAtom s]
binderToLP (PReg x s) = LPList (LPAtom x : depTypeToLP s)

stmtToLP :: Stmt -> LispPP
stmtToLP (StepSort x) = LPList [LPAtom "sort", LPAtom x]
stmtToLP (StepTerm x) = LPList [LPAtom "term", LPAtom x]
stmtToLP (StepAxiom x) = LPList [LPAtom "axiom", LPAtom x]
stmtToLP (StmtDef x bis ret ds val st) = LPList [
  LPAtom $ if st then "pub" else "local", LPAtom "def",
  LPAtom x, LPList (binderToLP <$> bis), LPList (depTypeToLP ret),
  LPList ((\(d, s) -> LPList [LPAtom d, LPAtom s]) <$> ds),
  LPLarge $ sExprToLP val]
stmtToLP (StmtThm x bis hs ret ds pf st) = LPList [
  LPAtom $ if st then "pub" else "local", LPAtom "theorem",
  LPAtom x, LPList (binderToLP <$> bis),
  LPLarge $ LPList ((\(h, ht) -> LPLarge $ LPList [LPAtom h, sExprToLP ht]) <$> hs),
  sExprToLP ret,
  LPList ((\(d, s) -> LPList [LPAtom d, LPAtom s]) <$> ds),
  LPLarge $ proofToLP pf]
stmtToLP (StepInout (VIKString False)) = LPList [LPAtom "input", LPAtom "string"]
stmtToLP (StepInout (VIKString True)) = LPList [LPAtom "output", LPAtom "string"]

ppLisp :: LispPP -> Doc Void
ppLisp (LPAtom t) = pretty t
ppLisp (LPLarge e) = ppLisp e
ppLisp (LPList []) = "()"
ppLisp (LPList (e : es)) = parens $ nest 2 $ soft e es where

  soft :: LispPP -> [LispPP] -> Doc Void
  soft e1 [] = ppLisp e1
  soft e1 (LPLarge e2 : es') = hard e1 (e2 : es')
  soft e1 (e2 : es') = ppLisp e1 <> softline <> soft e2 es'

  hard :: LispPP -> [LispPP] -> Doc Void
  hard e1 [] = ppLisp e1
  hard e1 (e2 : es') = ppLisp e1 <> line <> hard e2 es'

instance Show LispPP where
  showsPrec _ = renderShowS .
    layoutPretty (LayoutOptions Unbounded) . ppLisp

instance Show Conv where showsPrec n pf = showsPrec n (convToLP pf)
instance Show Proof where showsPrec n pf = showsPrec n (proofToLP pf)
instance Show Stmt where showsPrec n st = showsPrec n (stmtToLP st)
