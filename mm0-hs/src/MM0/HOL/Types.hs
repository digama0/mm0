module MM0.HOL.Types (module MM0.HOL.Types, Ident, Sort, WithComment(..)) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import MM0.Kernel.Environment (Ident, Sort, WithComment(..))
import MM0.Util

-- An SType is a type of the form s1 -> ... sn -> t where
-- si and t are basic types (sorts). Regular MM0 variables have an SType
data SType = SType [Sort] Sort deriving (Eq, Ord)

instance Show SType where
  showsPrec _ (SType [] s) = (T.unpack s ++)
  showsPrec n (SType ss s) = showParen (n > 0) $
    \r -> foldr (\x r' -> T.unpack x ++ " -> " ++ r') (T.unpack s ++ r) ss

-- An HType is a type of the form s1 -> ... sn -> t where
-- si and t are simple types. MM0 term constructors have this type.
-- Full HOL is not needed.
data HType = HType [SType] SType

instance Show HType where
  showsPrec n (HType [] s) = showsPrec n s
  showsPrec n (HType ss s) = showParen (n > 0) $
    \r -> foldr (\x r' -> showsPrec 1 x (" -> " ++ r')) (shows s r) ss

showBinds :: String -> (a -> ShowS) -> [(Ident, a)] -> ShowS
showBinds _ _ [] = id
showBinds c g (v:vs) =
  let f (x, t) r = '(' : T.unpack x ++ ": " ++ g t (')' : r) in
  \r -> c ++ f v (foldr (\v' -> (' ' :) . f v') (". " ++ r) vs)

showBinds' :: (a -> ShowS) -> [(Ident, a)] -> ShowS
showBinds' g vs r = foldr (\(x, t) r' -> " (" ++ T.unpack x ++ ": " ++ g t (')' : r')) r vs

data SLam = SLam [(Ident, Sort)] Term deriving (Eq)

instance Show SLam where
  showsPrec n (SLam [] e) = showsPrec n e
  showsPrec n (SLam vs e) = showParen (n > 0) $
    showBinds "\\" ((++) . T.unpack) vs . shows e

data Term =
    LVar Ident
  | RVar Ident [Ident]
  | HApp Ident [SLam] [Ident]
  | HTSorry
  deriving (Eq)

instance Show Term where
  showsPrec _ (LVar v) = (T.unpack v ++)
  showsPrec _ (RVar v []) = (T.unpack v ++)
  showsPrec n (RVar v xs) = showParen (n > 0) $
    (T.unpack v ++) . flip (foldr (\x -> ((' ' : T.unpack x) ++))) xs
  showsPrec _ (HApp t [] []) = (T.unpack t ++)
  showsPrec n (HApp t es xs) = showParen (n > 0) $ (T.unpack t ++) .
    flip (foldr (\e -> (' ' :) . showsPrec 1 e)) es .
    flip (foldr (\x -> ((' ' : T.unpack x) ++))) xs
  showsPrec _ HTSorry = ("?" ++)

-- A GType is the type of a MM0 statement. It corresponds to the HOL statement
-- !xs. |- t, where t is a wff term depending on xs.
data GType = GType [(Ident, Sort)] Term deriving (Eq)

instance Show GType where
  showsPrec _ (GType [] e) = ("|- " ++) . shows e
  showsPrec n (GType vs e) = showParen (n > 0) $
    showBinds "!" ((++) . T.unpack) vs . ("|- " ++) . shows e

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
    showBinds "\\" ((++) . T.unpack) vs . shows e

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
  | HForget Term HProofLam
  -- ^ Given a proof of !xs. |- ph, where ph does not depend on xs,
  -- produce a proof of |- ph. The provided term is ph.
  -- Requires that the sort not be free (i.e. is inhabited)
  | HConv HConv HProof
  -- ^ Proof by conversion (definitional equality).
  -- From |- ph = ph' and |- ph infer |- ph'.
  -- Some HOL systems use a built in equality, for others this is automatic
  | HSorry

instance Show HProof where
  showsPrec _ (HHyp v []) = (T.unpack v ++)
  showsPrec n (HHyp v xs) = showParen (n > 0) $
    (T.unpack v ++) . flip (foldr (\x -> ((' ' : T.unpack x) ++))) xs
  showsPrec _ (HThm t [] [] []) = (T.unpack t ++)
  showsPrec n (HThm t es hs xs) = showParen (n > 0) $ (T.unpack t ++) .
    flip (foldr (\e -> (' ' :) . showsPrec 1 e)) es .
    flip (foldr (\e -> (' ' :) . showsPrec 1 e)) hs .
    flip (foldr (\x -> ((' ' : T.unpack x) ++))) xs
  showsPrec n (HSave v p xs) = showParen (n > 0) $ \r ->
    "let " ++ T.unpack v ++ " = " ++ shows p (" in " ++ shows (HHyp v xs) r)
  showsPrec n (HForget _ p) = showParen (n > 0) $ ("forget " ++) . shows p
  showsPrec n (HConv c p) = showParen (n > 0) $
    ("mp " ++) . shows c . (' ' :) . shows p
  showsPrec _ HSorry = ("?" ++)

data HConvLam = HConvLam [(Ident, Sort)] HConv

instance Show HConvLam where
  showsPrec n (HConvLam [] e) = showsPrec n e
  showsPrec n (HConvLam vs e) = showParen (n > 0) $
    showBinds "\\" ((++) . T.unpack) vs . shows e

data HConv =
    CRefl Term
  -- ^ |- e = e
  | CSymm HConv
  -- ^ |- e1 = e2 => |- e2 = e1
  | CTrans HConv HConv
  -- ^ |- e1 = e2 => |- e2 = e3 => |- e1 = e3
  | CCong Ident [HConvLam] [Ident]
  -- ^ |- ei = ei' => |- T es xs = T es' xs
  | CDef Ident [SLam] [Ident]
  -- ^ |- T es xs = D(es, xs), where D is the definition of T

instance Show HConv where
  showsPrec _ (CRefl _) = ("rfl" ++)
  showsPrec _ (CSymm c) = ('-' :) . showsPrec 1 c
  showsPrec n (CTrans c1 c2) = showParen (n > 0) $
    shows c1 . (" . " ++) . shows c2
  showsPrec n (CCong t cs xs) = showParen (n > 0) $ ("ap " ++) . (T.unpack t ++) .
    flip (foldr (\e -> (' ' :) . showsPrec 1 e)) cs .
    flip (foldr (\x -> ((' ' : T.unpack x) ++))) xs
  showsPrec n (CDef t es xs) = showParen (n > 0) $ ("delta " ++) . (T.unpack t ++) .
    flip (foldr (\e -> (' ' :) . showsPrec 1 e)) es .
    flip (foldr (\x -> ((' ' : T.unpack x) ++))) xs

data HDecl =
    HDSort Sort
  -- ^ Introduce a new sort
  | HDTerm Ident HType
  -- ^ Define a new term constructor T
  | HDDef Ident [(Ident, SType)] [(Ident, Sort)] Sort Term
  -- ^ Define !As. !xs. T As xs = t
  | HDThm Ident TType (Maybe ([Ident], HProof))
  -- ^ Prove a theorem or assert an axiom Th : !As. |- Gs => !xs. |- ph.
  -- The proof \hs. P, if given, derives |- ph in the context with As, xs, hs:Gs.

instance Show HDecl where
  show (HDSort s) = "sort " ++ T.unpack s
  show (HDTerm t ty) = "term " ++ T.unpack t ++ ": " ++ show ty
  show (HDDef t rv lv s val) =
    "def " ++ T.unpack t ++ showBinds' shows rv (showBinds' ((++) . T.unpack) lv
      (": " ++ T.unpack s ++ " := " ++ show val))
  show (HDThm t ty Nothing) = "axiom " ++ T.unpack t ++ ": " ++ show ty
  show (HDThm t (TType vs hs (GType ss ret)) (Just (gs, p))) =
    ("theorem " ++) $ (T.unpack t ++) $
    showBinds' shows vs $ showBinds' shows (zip gs hs) $
    showBinds' ((++) . T.unpack) ss $ (": |- " ++) $ shows ret $ " :=\n" ++ show p

fvLLam :: SLam -> S.Set Ident
fvLLam (SLam vs t) = foldr S.delete (fvLTerm t) (fst <$> vs)

fvLTerm :: Term -> S.Set Ident
fvLTerm (LVar x) = S.singleton x
fvLTerm (RVar _ xs) = S.fromList xs
fvLTerm (HApp _ ls xs) = foldMap fvLLam ls <> S.fromList xs
fvLTerm HTSorry = S.empty

fvRLam :: SLam -> S.Set Ident
fvRLam (SLam _ t) = fvRTerm t

fvRTerm :: Term -> S.Set Ident
fvRTerm (LVar _) = S.empty
fvRTerm (RVar v _) = S.singleton v
fvRTerm (HApp _ ls _) = foldMap fvRLam ls
fvRTerm HTSorry = S.empty

fvLam :: SLam -> S.Set Ident
fvLam (SLam vs t) = foldr S.delete (fvTerm t) (fst <$> vs)

fvTerm :: Term -> S.Set Ident
fvTerm (LVar x) = S.singleton x
fvTerm (RVar v xs) = S.insert v $ S.fromList xs
fvTerm (HApp _ ls xs) = foldMap fvLam ls <> S.fromList xs
fvTerm HTSorry = S.empty

variant :: S.Set Ident -> Ident -> Ident
variant s v = if S.member v s then variant s (v <> "'") else v

substAbs :: M.Map Ident SLam -> [(Ident, Sort)] -> Term -> ([(Ident, Sort)], Term)
substAbs m vs1 t = go vs1 M.empty where
  free :: S.Set Ident
  free = foldMap (fvLam . (m M.!)) (fvRTerm t)
  go [] vm = ([], substTerm m $ vsubstTerm vm t)
  go ((v, s) : vs) vm =
    let v' = variant free v
        (vs', t') = go vs (if v' == v then vm else M.insert v v' vm) in
    ((v', s) : vs', t')

substGType :: M.Map Ident SLam -> GType -> GType
substGType m (GType ss r) = uncurry GType (substAbs m ss r)

substSLam :: M.Map Ident SLam -> SLam -> SLam
substSLam m (SLam vs t) = uncurry SLam (substAbs m vs t)

substTerm :: M.Map Ident SLam -> Term -> Term
substTerm _ v@(LVar _) = v
substTerm m (RVar v ys) = case m M.! v of
  SLam ss t -> vsubstTerm (M.fromList (zip (fst <$> ss) ys)) t
substTerm m (HApp t es vs) = HApp t (substSLam m <$> es) vs
substTerm _ HTSorry = HTSorry

vsubst :: M.Map Ident Ident -> Ident -> Ident
vsubst m v = M.findWithDefault v v m

vsubstSLam :: M.Map Ident Ident -> SLam -> SLam
vsubstSLam m1 (SLam vs1 t) = go m1 (S.fromList $ M.elems m1) vs1 where
  go :: M.Map Ident Ident -> S.Set Ident -> [(Ident, Sort)] -> SLam
  go m _ [] = SLam [] (vsubstTerm m t)
  go m free ((v, s) : vs) =
    if S.member v free then
      let v' = variant free v
          SLam vs' t' = go (M.insert v v' m)
            (S.insert v' (maybe free (`S.delete` free) (m M.!? v))) vs in
      SLam ((v', s) : vs') t'
    else
      let SLam vs' t' = go (M.delete v m)
            (maybe free (`S.delete` free) (m M.!? v)) vs in
      SLam ((v, s) : vs') t'

vsubstTerm :: M.Map Ident Ident -> Term -> Term
vsubstTerm m t | null m = t
vsubstTerm m (LVar x) = LVar (vsubst m x)
vsubstTerm m (RVar v xs) = RVar v (vsubst m <$> xs)
vsubstTerm m (HApp t es xs) = HApp t (vsubstSLam m <$> es) (vsubst m <$> xs)
vsubstTerm _ HTSorry = HTSorry

nfTerm :: S.Set Ident -> Term -> Bool
nfTerm s (LVar x) = S.notMember x s
nfTerm s (RVar _ xs) = all (`S.notMember` s) xs
nfTerm s (HApp _ es vs) = all (nfSLam s) es && all (`S.notMember` s) vs
nfTerm _ HTSorry = True

nfSLam :: S.Set Ident -> SLam -> Bool
nfSLam s (SLam vs t) = nfTerm (foldr S.delete s (fst <$> vs)) t

alphaVar :: M.Map Ident Ident -> Ident -> Ident -> Bool
alphaVar m x y = vsubst m x == y

alphaBind :: (M.Map Ident Ident -> Bool) -> M.Map Ident Ident -> [(Ident, Sort)] -> [(Ident, Sort)] -> Bool
alphaBind f = go where
  go m [] [] = f m
  go m ((x1, t1) : bs1) ((x2, t2) : bs2) =
    t1 == t2 && go (M.insert x1 x2 m) bs1 bs2
  go _ _ _ = False

alphaSLam :: M.Map Ident Ident -> SLam -> SLam -> Bool
alphaSLam m (SLam vs1 t1) (SLam vs2 t2) =
  alphaBind (\m' -> alphaTerm m' t1 t2) m vs1 vs2

alphaTerm :: M.Map Ident Ident -> Term -> Term -> Bool
alphaTerm m (LVar x) (LVar y) = alphaVar m x y
alphaTerm m (RVar v1 vs1) (RVar v2 vs2) = v1 == v2 && all2 (alphaVar m) vs1 vs2
alphaTerm m (HApp t1 es1 vs1) (HApp t2 es2 vs2) =
  t1 == t2 && all2 (alphaSLam m) es1 es2 && all2 (alphaVar m) vs1 vs2
alphaTerm _ _ _ = False

alphaGType :: GType -> GType -> Bool
alphaGType (GType ss1 r1) (GType ss2 r2) =
  alphaBind (\m' -> alphaTerm m' r1 r2) M.empty ss1 ss2
