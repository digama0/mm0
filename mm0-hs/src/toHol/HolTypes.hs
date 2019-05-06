module HolTypes where

import qualified Data.Map.Strict as M
import qualified Data.Sequence as Q
import qualified Data.Set as S
import Environment (Ident)

type Sort = Ident
-- An SType is a type of the form s1 -> ... sn -> t where
-- si and t are basic types (sorts). Regular MM0 variables have an SType
data SType = SType [Sort] Sort deriving (Eq)

instance Show SType where
  showsPrec n (SType [] s) = (s ++)
  showsPrec n (SType ss s) = showParen (n > 0) $
    \r -> foldr (\x r -> x ++ " -> " ++ r) (s ++ r) ss

-- An HType is a type of the form s1 -> ... sn -> t where
-- si and t are simple types. MM0 term constructors have this type.
-- Full HOL is not needed.
data HType = HType [SType] SType

instance Show HType where
  showsPrec n (HType [] s) = showsPrec n s
  showsPrec n (HType ss s) = showParen (n > 0) $
    \r -> foldr (\x r -> showsPrec 1 x (" -> " ++ r)) (shows s r) ss

showBinds :: String -> (a -> ShowS) -> [(Ident, a)] -> ShowS
showBinds _ _ [] = id
showBinds c g (v:vs) =
  let f (x, t) r = '(' : x ++ ": " ++ g t (')' : r) in
  \r -> c ++ f v (foldr (\v' -> (' ' :) . f v') (". " ++ r) vs)

showBinds' :: (a -> ShowS) -> [(Ident, a)] -> ShowS
showBinds' g vs r = foldr (\(x, t) r -> " (" ++ x ++ ": " ++ g t (')' : r)) r vs

data SLam = SLam [(Ident, Sort)] Term deriving (Eq)

instance Show SLam where
  showsPrec n (SLam [] e) = showsPrec n e
  showsPrec n (SLam vs e) = showParen (n > 0) $ showBinds "\\" (++) vs . shows e

data Term =
    LVar Ident
  | RVar Ident [Ident]
  | HApp Ident [SLam] [Ident]
  | HTSorry
  deriving (Eq)

instance Show Term where
  showsPrec n (LVar v) = (v ++)
  showsPrec n (RVar v []) = (v ++)
  showsPrec n (RVar v xs) = showParen (n > 0) $
    flip (foldr (\x -> ((' ' : x) ++))) xs
  showsPrec n (HApp t [] []) = (t ++)
  showsPrec n (HApp t es xs) = showParen (n > 0) $ (t ++) .
    flip (foldr (\e -> (' ' :) . showsPrec 1 e)) es .
    flip (foldr (\x -> ((' ' : x) ++))) xs
  showsPrec n HTSorry = ("?" ++)

-- A GType is the type of a MM0 statement. It corresponds to the HOL statement
-- !xs. |- t, where t is a wff term depending on xs.
data GType = GType [(Ident, Sort)] Term deriving (Eq)

instance Show GType where
  showsPrec _ (GType [] e) = ("|- " ++) . shows e
  showsPrec n (GType vs e) = showParen (n > 0) $
    showBinds "!" (++) vs . ("|- " ++) . shows e

-- A TType is the type of a MM0 theorem. The STypes are the regular variables,
-- and the GTypes are the hypotheses. It corresponds to the HOL statement
-- !As. G1 -> ... -> Gn -> G' where the A's are higher order (SType) variables
-- and the G's are GTypes.
data TType = TType [(Ident, SType)] [GType] GType

instance Show TType where
  showsPrec n (TType vs hs ret) = showParen (n > 0) $
    showBinds "!" shows vs .
    flip (foldr (\x r -> showsPrec 1 x (" => " ++ r))) hs . shows ret

-- A proof of !xs. |- ph. Variable lambdas are only allowed in certain
-- positions in HProof, so we make that explicit.
data HProofLam = HProofLam [(Ident, Sort)] HProof

instance Show HProofLam where
  showsPrec n (HProofLam [] e) = showsPrec n e
  showsPrec n (HProofLam vs e) = showParen (n > 0) $
    showBinds "\\" (++) vs . shows e

data HProof =
    HHyp Ident [Ident]
  -- ^ |- [ys/xs] ph, if (!xs. |- ph) is hypothesis i
  -- in the proof context. In MM0 xs and ys will always be the same
  | HThm Ident [SLam] [HProofLam] [Ident]
  -- ^ If T : !As. G1 -> ... -> Gn -> !xs. |- ph, given expressions Ss and
  -- subproofs of [Ss/As] Gi, and variables ys, produce a proof of
  -- [ys/xs] [Ss/As] ph. In some HOL systems this requires an additional beta rule
  | HSave Ident HProofLam [Ident]
  -- ^ Abstract and save this proof in the local dictionary.
  -- Similar to dict[n] <- !xs. |- ph ; return |- [ys/xs] ph.
  -- In MM0 xs and ys are the same. The saved value is accessible via HHyp
  | HForget HProofLam
  -- ^ Given a proof of !xs. |- ph, where ph does not depend on xs,
  -- produce a proof of |- ph.
  -- Requires that the sort not be free (i.e. is inhabited)
  | HConv HConv HProof
  -- ^ Proof by conversion (definitional equality).
  -- From |- ph = ph' and |- ph infer |- ph'.
  -- Some HOL systems use a built in equality, for others this is automatic
  | HSorry

instance Show HProof where
  showsPrec n (HHyp v []) = (v ++)
  showsPrec n (HHyp v xs) = showParen (n > 0) $
    flip (foldr (\x -> ((' ' : x) ++))) xs
  showsPrec n (HThm t [] [] []) = (t ++)
  showsPrec n (HThm t es hs xs) = showParen (n > 0) $ (t ++) .
    flip (foldr (\e -> (' ' :) . showsPrec 1 e)) es .
    flip (foldr (\e -> (' ' :) . showsPrec 1 e)) hs .
    flip (foldr (\x -> ((' ' : x) ++))) xs
  showsPrec n (HSave v p xs) = showParen (n > 0) $ \r ->
    "let " ++ v ++ " = " ++ shows p (" in " ++ shows (HHyp v xs) r)
  showsPrec n (HForget p) = showParen (n > 0) $ ("forget " ++) . shows p
  showsPrec n (HConv c p) = showParen (n > 0) $
    ("mp " ++) . shows c . (' ' :) . shows p
  showsPrec n HSorry = ("?" ++)

data HConvLam = HConvLam [(Ident, Sort)] HConv

instance Show HConvLam where
  showsPrec n (HConvLam [] e) = showsPrec n e
  showsPrec n (HConvLam vs e) = showParen (n > 0) $
    showBinds "\\" (++) vs . shows e

data HConv =
    CRefl Term
  -- ^ |- e = e
  | CSymm HConv
  -- ^ |- e1 = e2 => |- e2 = e1
  | CTrans HConv HConv
  -- ^ |- e1 = e2 => |- e2 = e3 => |- e1 = e3
  | CCong Ident [HConvLam] [Ident]
  -- ^ |- ei = ei' => |- T es xs = T es' xs
  | CDef Ident [SLam] [Ident] [Ident]
  -- ^ |- T es xs = D es xs ys, where ys names the bound vars
  -- in the definition D of T

instance Show HConv where
  showsPrec n (CRefl e) = ("rfl" ++)
  showsPrec n (CSymm c) = ('-' :) . showsPrec 1 c
  showsPrec n (CTrans c1 c2) = showParen (n > 0) $
    shows c1 . (" . " ++) . shows c2
  showsPrec n (CCong t cs xs) = showParen (n > 0) $ ("ap " ++) . (t ++) .
    flip (foldr (\e -> (' ' :) . showsPrec 1 e)) cs .
    flip (foldr (\x -> ((' ' : x) ++))) xs
  showsPrec n (CDef t es xs _) = showParen (n > 0) $ ("delta " ++) . (t ++) .
    flip (foldr (\e -> (' ' :) . showsPrec 1 e)) es .
    flip (foldr (\x -> ((' ' : x) ++))) xs

data HDecl =
    HDSort Sort
  -- ^ Introduce a new sort
  | HDTerm Ident HType
  -- ^ Define a new term constructor T
  | HDDef Ident [(Ident, SType)] [(Ident, Sort)] Term [Ident]
  -- ^ Define !As. !xs. T As xs = t{ys}, where ys gives the names of
  -- bound variables in t
  | HDThm Ident TType (Maybe ([Ident], HProof))
  -- ^ Prove a theorem or assert an axiom Th : !As. |- Gs => !xs. |- ph.
  -- The proof, if given, derives |- ph in the context with As, xs, Gs.

instance Show HDecl where
  show (HDSort s) = "sort " ++ s
  show (HDTerm t ty) = "term " ++ t ++ ": " ++ show ty
  show (HDDef t rv lv val _) =
    "def " ++ t ++ showBinds' shows rv (showBinds' (++) lv (" := " ++ show val))
  show (HDThm t ty Nothing) = "axiom " ++ t ++ ": " ++ show ty
  show (HDThm t (TType vs hs (GType ss ret)) (Just (gs, p))) =
    ("theorem " ++) $ (t ++) $
    showBinds' shows vs $ showBinds' shows (zip gs hs) $
    showBinds' (++) ss $ (": |- " ++) $ shows ret $ " :=\n" ++ show p

substGType :: M.Map Ident SLam -> GType -> GType
substGType m (GType ss r) = GType ss (substTerm m r)

substSLam :: M.Map Ident SLam -> SLam -> SLam
substSLam m (SLam vs t) = SLam vs (substTerm m t)

substTerm :: M.Map Ident SLam -> Term -> Term
substTerm m v@(LVar _) = v
substTerm m (RVar v ys) = case m M.! v of
  SLam ss t -> vsubstTerm (M.fromList (zip (fst <$> ss) ys)) t
substTerm m (HApp t es vs) = HApp t (substSLam m <$> es) vs

vsubst :: M.Map Ident Ident -> Ident -> Ident
vsubst m v = M.findWithDefault v v m

vsubstSLam :: M.Map Ident Ident -> SLam -> SLam
vsubstSLam m (SLam vs t) = SLam vs $
  vsubstTerm (foldr M.delete m (fst <$> vs)) t

vsubstTerm :: M.Map Ident Ident -> Term -> Term
vsubstTerm m (LVar x) = LVar (vsubst m x)
vsubstTerm m v@(RVar _ _) = v
vsubstTerm m (HApp t es vs) = HApp t (vsubstSLam m <$> es) (vsubst m <$> vs)

nfTerm :: S.Set Ident -> Term -> Bool
nfTerm s (LVar x) = S.notMember x s
nfTerm s (RVar _ xs) = all (`S.notMember` s) xs
nfTerm s (HApp t es vs) = all (nfSLam s) es && all (`S.notMember` s) vs

nfSLam :: S.Set Ident -> SLam -> Bool
nfSLam s (SLam vs t) = nfTerm (foldr S.delete s (fst <$> vs)) t

alphaSLam :: M.Map Ident Ident -> SLam -> SLam
alphaSLam m (SLam vs t) =
  SLam ((\(x, s) -> (vsubst m x, s)) <$> vs) (alphaTerm m t)

alphaTerm :: M.Map Ident Ident -> Term -> Term
alphaTerm m (LVar x) = LVar (vsubst m x)
alphaTerm m (RVar v vs) = RVar v (vsubst m <$> vs)
alphaTerm m (HApp t es vs) = HApp t (alphaSLam m <$> es) (vsubst m <$> vs)

allInTerm :: S.Set Ident -> Term -> Bool
allInTerm s (LVar x) = S.member x s
allInTerm s (RVar _ xs) = all (`S.member` s) xs
allInTerm s (HApp t es vs) = all (allInSLam s) es && all (`S.member` s) vs

allInSLam :: S.Set Ident -> SLam -> Bool
allInSLam s (SLam vs t) = all (`S.member` s) (fst <$> vs) && allInTerm s t
