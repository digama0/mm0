{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module CElaborator (elaborate, ErrorLevel(..), ElabError(..)) where

import Control.Monad.State
import Data.List
import Data.Bits
import Data.Word8
import Data.Maybe
import qualified Data.HashMap.Strict as H
import qualified Data.Set as S
import qualified Data.Vector.Unboxed as U
import qualified Data.Text as T
import CParser (ParseError)
import CAST
import CEnv
import CMathParser
import Util

elaborate :: [ParseError] -> AST -> IO (Env, [ElabError])
elaborate errs ast = do
  (_, env, errs') <- runElab (mapM_ elabStmt ast) (toElabError <$> errs)
  return (env, errs')

elabStmt :: AtPos Stmt -> Elab ()
elabStmt (AtPos pos s) = resuming $ case s of
  Sort px x sd -> addSort px x sd
  Decl vis dk px x bis ret v -> addDecl vis dk px x bis ret v
  Notation (Delimiter cs Nothing) -> lift $ addDelimiters cs cs
  Notation (Delimiter ls (Just rs)) -> lift $ addDelimiters ls rs
  Notation (Prefix px x tk prec) -> addPrefix px x tk prec
  Notation (Infix r px x tk prec) -> addInfix r px x tk prec
  Notation (NNotation px x bis _ lits) -> addNotation px x bis lits
  Notation (Coercion px x s1 s2) -> addCoercion px x s1 s2
  _ -> unimplementedAt pos

checkNew :: ErrorLevel -> Offset -> T.Text -> (v -> Offset) -> T.Text ->
  H.HashMap T.Text v -> ElabM (v -> H.HashMap T.Text v)
checkNew l o msg f k m = case H.lookup k m of
  Nothing -> return (\v -> H.insert k v m)
  Just a -> do
    reportErr $ ElabError l o o msg [(f a, f a, "previously declared here")]
    mzero

addSort :: Offset -> T.Text -> SortData -> ElabM ()
addSort px x sd = do
  ins <- gets eSorts >>= checkNew ELError px
    ("duplicate sort declaration '" <> x <> "'") (\(_, i, _) -> i) x
  n <- next
  modify $ \env -> env {
    eSorts = ins (n, px, sd),
    eProvableSorts = (guard (sProvable sd) >> [x]) ++ eProvableSorts env }

inferDepType :: AtDepType -> ElabM ()
inferDepType (AtDepType (AtPos o t) ts) = do
  lift $ resuming $ do
    (_, _sd) <- try (now >>= getSort t) >>=
      fromJustAt o ("sort '" <> t <> "' not declared")
    -- TODO: check sd
    return ()
  lift $ modifyInfer $ \ic -> ic {
    icDependents = foldl' (\m (AtPos i x) ->
      H.alter (Just . maybe [i] (i:)) x m) (icDependents ic) ts }

inferBinder :: Binder -> ElabM (Maybe (Offset, Local, InferResult))
inferBinder bi@(Binder o l oty) = case oty of
  Nothing -> Nothing <$ addVar True
  Just (TType ty) -> inferDepType ty >> Nothing <$ addVar False
  Just (TFormula f) -> do
    ir <- parseMath f >>= inferQExprProv
    return $ Just (o, l, ir)
  where

  addVar :: Bool -> ElabM ()
  addVar noType = do
    locals <- gets (icLocals . eInfer)
    locals' <- case localName l of
      Nothing -> do
        when noType $ escapeAt o "cannot infer variable type"
        return $ locals
      Just n -> do
        ins <- checkNew ELWarning o
          ("variable '" <> n <> "' shadows previous declaration")
          liOffset n locals
        return (ins (LIOld bi Nothing))
    lift $ modifyInfer $ \ic -> ic {icLocals = locals'}

addDecl :: Visibility -> DeclKind -> Offset -> T.Text ->
  [Binder] -> Maybe [Type] -> Maybe LispVal -> ElabM ()
addDecl vis dk px x bis ret v = do
  let (bis', ret') = unArrow bis ret
  decl <- withInfer $ do
    fmlas <- catMaybes <$> mapM inferBinder bis'
    (pbs, hs, dums) <- buildBinders (dk == DKDef) bis' fmlas
    decl <- case (dk, ret', v) of
      (DKDef, Just (TType ty), Nothing) -> do
        inferDepType ty
        reportAt px ELWarning "definition has no body; axiomatizing"
        unless (null hs) $ error "impossible"
        return (DTerm pbs (unDepType ty))
      (DKDef, _, Just (LFormula f)) -> do
        unless (null hs) $ error "impossible"
        let ret'' = case ret' of Just (TType ty) -> Just ty; _ -> Nothing
        forM_ ret'' inferDepType
        IR _ v' s _ <- parseMath f >>=
          inferQExpr ((\(AtDepType s _) -> (unPos s, False)) <$> ret'')
        vs <- case ret'' of
          Just (AtDepType (AtPos o _) avs) -> do
            vs' <- defcheckExpr pbs v'
            let vs1 = unPos <$> avs
            let bad = foldr S.delete vs' vs1
            unless (S.null bad) $
              escapeAt o ("definition has undeclared free variable(s): " <>
                T.intercalate ", " (S.toList bad))
            return vs1
          Nothing -> S.toList <$> defcheckExpr pbs v'
        return (DDef vis pbs (DepType s vs) dums v')
      (DKDef, _, Just _) -> unimplementedAt px
      (DKTerm, Just (TType ty), _) -> do
        inferDepType ty
        unless (null hs) $ error "impossible"
        return (DTerm pbs (unDepType ty))
      (DKAxiom, Just (TFormula f), _) -> do
        IR _ eret _ _ <- parseMath f >>= inferQExprProv
        return (DAxiom pbs ((\(_, _, h) -> h) <$> hs) eret)
      (DKTheorem, Just (TFormula f), _) -> do
        IR _ eret _ _ <- parseMath f >>= inferQExprProv
        case v of
          Nothing -> do
            reportAt px ELWarning "theorem proof missing"
            return (DAxiom pbs ((\(_, _, h) -> h) <$> hs) eret)
          Just lv -> do
            fork <- forkElabM (return lv)
            return (DTheorem vis pbs ((\(_, _, h) -> h) <$> hs) eret fork)
      _ -> unimplementedAt px
    checkVarRefs >> return decl
  ins <- gets eDecls >>= checkNew ELError px
    ("duplicate " <> T.pack (show dk) <> " declaration '" <> x <> "'") (\(_, i, _) -> i) x
  n <- next
  modify $ \env -> env {eDecls = ins (n, px, decl)}

unArrow :: [Binder] -> Maybe [Type] -> ([Binder], Maybe Type)
unArrow bis Nothing = (bis, Nothing)
unArrow bis (Just tys') = mapFst (bis ++) (go tys') where
  go [] = undefined
  go [ty] = ([], Just ty)
  go (ty:tys) = mapFst (Binder (tyOffset ty) LAnon (Just ty) :) (go tys)

addDelimiters :: [Char] -> [Char] -> Elab ()
addDelimiters ls rs = modifyPE $ go 2 rs . go 1 ls where
  go w cs pe = pe { pDelims = Delims $ arr U.// (f <$> cs) } where
    Delims arr = pDelims pe
    f :: Char -> (Int, Word8)
    f c = let i = fromEnum (toEnum (fromEnum c) :: Word8)
          in (i, (U.unsafeIndex arr i) .|. w)

mkLiterals :: Int -> Prec -> Int -> [PLiteral]
mkLiterals 0 _ _ = []
mkLiterals 1 p n = [PVar n p]
mkLiterals i p n = PVar n PrecMax : mkLiterals (i-1) p (n+1)

addPrefix :: Offset -> T.Text -> Const -> Prec -> ElabM ()
addPrefix px x tk prec = do
  (_, bis, _) <- try (now >>= getTerm x) >>=
    fromJustAt px ("term '" <> x <> "' not declared")
  insertPrec tk prec
  insertPrefixInfo tk (PrefixInfo (cOffs tk) x (mkLiterals (length bis) prec 0))

addInfix :: Bool -> Offset -> T.Text -> Const -> Prec -> ElabM ()
addInfix r px x tk prec = do
  (_, bis, _) <- try (now >>= getTerm x) >>=
    fromJustAt px ("term '" <> x <> "' not declared")
  guardAt px ("'" <> x <> "' must be a binary operator") (length bis == 2)
  insertPrec tk prec
  insertInfixInfo tk (InfixInfo (cOffs tk) x r)

addNotation :: Offset -> T.Text -> [Binder] -> [AtPos Literal] -> ElabM ()
addNotation px x bis = \lits -> do
  (_, bis', _) <- try (now >>= getTerm x) >>=
    fromJustAt px ("term '" <> x <> "' not declared")
  unless (length bis == length bis') $
    escapeAt px ("term '" <> x <> "' has " <> T.pack (show (length bis')) <>
      " arguments, expected " <> T.pack (show (length bis)))
  (c, ti) <- processLits lits
  insertPrefixInfo c (PrefixInfo px x ti)
  where

  binderMap :: H.HashMap VarName Int
  binderMap = go bis 0 H.empty where
    go [] _ m = m
    go (Binder _ l _ : bs) n m =
      go bs (n+1) $ maybe m (\v -> H.insert v n m) (localName l)

  processLits :: [AtPos Literal] -> ElabM (Const, [PLiteral])
  processLits (AtPos _ (NConst c p) : lits') =
      insertPrec c p >> (,) c <$> go lits' where
    go :: [AtPos Literal] -> ElabM [PLiteral]
    go [] = return []
    go (AtPos _ (NConst c'@(Const _ tk) q) : lits) =
      insertPrec c' q >> (PConst tk :) <$> go lits
    go (AtPos o (NVar v) : lits) = do
      q <- case lits of
        [] -> return p
        (AtPos _ (NConst _ (Prec q)) : _)
          | q < maxBound -> return (Prec (q + 1))
        (AtPos o' (NConst _ _) : _) ->
          escapeAt o' "notation infix prec max not allowed"
        (AtPos _ (NVar _) : _) -> return PrecMax
      n <- fromJustAt o "notation variable not found" (H.lookup v binderMap)
      (PVar n q :) <$> go lits
  processLits (AtPos o _ : _) = escapeAt o "notation must begin with a constant"
  processLits [] = error "empty notation"

addCoercion :: Offset -> T.Text -> Sort -> Sort -> ElabM ()
addCoercion px x s1 s2 = do
  try (now >>= getTerm x) >>= \case
    Nothing -> escapeAt px ("term '" <> x <> "' not declared")
    Just (_, [PReg _ (DepType s1' [])], DepType s2' [])
      | s1 == s1' && s2 == s2' -> addCoe (Coe1 px x) s1 s2
    _ -> escapeAt px ("coercion '" <> x <> "' does not match declaration")

insertPrec :: Const -> Prec -> ElabM ()
insertPrec (Const o tk) p = do
  env <- get
  case H.lookup tk (pPrec (ePE env)) of
    Just (i, p') | p /= p' ->
      reportErr $ ElabError ELError o o
        ("incompatible precedence for '" <> tk <> "'")
        [(i, i, "previously declared here")]
    _ -> lift $ modifyPE $ \e -> e {pPrec = H.insert tk (o, p) (pPrec e)}

checkToken :: Const -> ElabM ()
checkToken (Const _ tk) | T.length tk == 1 = return ()
checkToken (Const o tk) = do
  delims <- gets (pDelims . ePE)
  guardAt o ("invalid token '" <> tk <> "'")
    (T.all (not . (`testBit` 1) . delimVal delims) (T.tail tk) &&
     T.all (not . (`testBit` 0) . delimVal delims) (T.init tk))

insertPrefixInfo :: Const -> PrefixInfo -> ElabM ()
insertPrefixInfo c@(Const o tk) ti = do
  checkToken c
  env <- get
  ins <- checkNew ELError o ("token '" <> tk <> "' already declared")
    (\(PrefixInfo i _ _) -> i) tk (pPrefixes (ePE env))
  lift $ modifyPE $ \e -> e {pPrefixes = ins ti}

insertInfixInfo :: Const -> InfixInfo -> ElabM ()
insertInfixInfo c@(Const o tk) ti = do
  checkToken c
  env <- get
  ins <- checkNew ELError o ("token '" <> tk <> "' already declared")
    (\(InfixInfo i _ _) -> i) tk (pInfixes (ePE env))
  lift $ modifyPE $ \e -> e {pInfixes = ins ti}

app1 :: TermName -> SExpr -> SExpr
app1 t e = App t [e]

data InferResult = IR Offset SExpr Sort Bool deriving (Show)
coerce :: Maybe (Sort, Bool) -> InferResult -> ElabM InferResult
coerce (Just (s2, bd2)) (IR o e s1 bd1) | s1 == s2 && (bd1 || not bd2) =
  return (IR o e s2 bd2)
coerce (Just (_, True)) (IR o _ _ _) =
  escapeAt o "type error, expected bound variable, got expression"
coerce (Just (s2, False)) (IR o e s1 _) =
  try (getCoe app1 s1 s2) >>= \case
    Just c -> return (IR o (c e) s2 False)
    Nothing -> escapeAt o ("type error, expected " <> s2 <>
      ", got " <> T.pack (show e) <> ": " <> s1)
coerce Nothing r = return r

inferQExpr :: Maybe (Sort, Bool) -> QExpr -> ElabM InferResult
inferQExpr tgt q = inferQExpr' tgt q >>= coerce tgt

inferQExpr' :: Maybe (Sort, Bool) -> QExpr -> ElabM InferResult
inferQExpr' tgt (QApp (AtPos o t) ts) = do
  var <- gets (H.lookup t . icLocals . eInfer)
  tm <- try (now >>= getTerm t)
  let returnVar :: Sort -> Bool -> ElabM a -> ElabM InferResult
      returnVar s bd m = do
        unless (null ts) $ escapeAt o (t <> " is not a function")
        (IR o (SVar t) s bd) <$ m
  case (var, tm) of
    (Just (LIOld (Binder _ l (Just (TType (AtDepType (AtPos _ s) _)))) _), _) ->
      returnVar s (isLCurly l) (return ())
    (Just (LIOld (Binder _ l _) (Just s)), _) ->
      returnVar s (isLCurly l) (return ())
    (Just (LIOld bi@(Binder _ l _) Nothing), _) -> do
      (s, _) <- fromJustAt o "cannot infer type" tgt
      returnVar s (isLCurly l) $ lift $ modifyInfer $ \ic -> ic {
        icLocals = H.insert t (LIOld bi (Just s)) (icLocals ic) }
    (_, Just (_, bis, DepType s _)) -> do
      let m = length ts
          n = length bis
          f bi t' = (\(IR _ e _ _) -> e) <$> inferQExpr (Just (hint bi)) t' where
            hint (PBound _ t2) = (t2, True)
            hint (PReg _ (DepType t2 _)) = (t2, False)
      unless (m == n) $ escapeAt o ("term '" <> t <> "' applied to " <>
        T.pack (show m) <> " arguments, expected " <> T.pack (show n))
      ts' <- zipWithM f bis ts
      return (IR o (App t ts') s False)
    (Just (LINew o1 bd1 s1), Nothing) -> do
      bd' <- case tgt of
        Just (s2, bd2) -> do
          unless (s1 == s2) $ escapeErr $ ElabError ELError o o
            ("inferred two types " <> s1 <> ", " <> s2 <> " for " <> t)
            [(o1, o1, "inferred " <> s1 <> " here"), (o, o, "inferred " <> s2 <> " here")]
          return (bd1 || bd2)
        _ -> return bd1
      returnVar s1 bd1 $ when (bd1 /= bd') $ lift $ modifyInfer $ \ic -> ic {
        icLocals = H.insert t (LINew o1 bd' s1) (icLocals ic) }
    (Nothing, Nothing) -> do
      (s, bd) <- fromJustAt o "cannot infer type" tgt
      returnVar s bd $ lift $ modifyInfer $ \ic -> ic {
        icLocals = H.insert t (LINew o bd s) (icLocals ic) }
inferQExpr' _tgt (QUnquote (AtPos o _l)) = unimplementedAt o

inferQExprProv :: QExpr -> ElabM InferResult
inferQExprProv q = gets eProvableSorts >>= \case
  [s] -> inferQExpr (Just (s, False)) q
  _ -> do
    IR o e s _ <- inferQExpr Nothing q
    try (getCoeProv app1 s) >>= \case
      Just (s2, c) -> return (IR o (c e) s2 False)
      Nothing -> escapeAt o ("type error, expected provable sort, got " <> s)

buildBinders :: Bool -> [Binder] -> [(Offset, Local, InferResult)] ->
  ElabM ([PBinder], [(Offset, Maybe VarName, SExpr)], [(Offset, VarName, Sort)])
buildBinders dum bis fs = do
  ic <- gets eInfer
  let locals = icLocals ic
      newvar :: VarName -> Offset -> Bool -> Sort -> Binder
      newvar v o bd s = Binder o l (Just (TType (AtDepType (AtPos o s) []))) where
        l = if bd then
          if not dum || H.member v (icDependents ic) then LBound v else LDummy v
        else LReg v
      bis1 = mapMaybe f bis where
        f bi@(Binder _ l _) = case localName l of
          Nothing -> Just ("_", bi)
          Just v -> case locals H.! v of
            LIOld (Binder _ _ (Just (TFormula _))) _ -> Nothing
            LIOld bi'@(Binder _ _ (Just (TType _))) _ -> Just (v, bi')
            LIOld bi'@(Binder _ _ Nothing) Nothing -> Just (v, bi')
            LIOld (Binder o l' Nothing) (Just t) ->
              Just (v, Binder o l' (Just (TType (AtDepType (AtPos o t) []))))
            LINew o bd s -> Just (v, newvar v o bd s)
      bisNew = sortOn fst (mapMaybe f (H.toList locals)) ++ bis1 where
        f (v, LINew o bd s) = Just (v, newvar v o bd s)
        f _ = Nothing
      bisDum = mapMaybe f bisNew where
        f (v, Binder o (LDummy _) (Just (TType (AtDepType (AtPos _ t) [])))) =
          Just (o, v, t)
        f _ = Nothing
      fmlas = mapMaybe (\(o, l, IR _ e _ _) -> Just (o, localName l, e)) fs
  bis' <- forM bisNew $ \case
    (v, Binder _ (LBound _) (Just (TType ty))) ->
      return $ Just $ PBound v (dSort (unDepType ty))
    (_, Binder _ (LDummy _) _) -> return Nothing
    (v, Binder _ _ (Just (TType ty))) ->
      return $ Just $ PReg v (unDepType ty)
    (_, Binder o _ Nothing) -> escapeAt o "could not infer type"
    _ -> return Nothing
  return (catMaybes bis', fmlas, bisDum)

checkVarRefs :: ElabM ()
checkVarRefs = do
  ic <- gets eInfer
  let errs = filter (not . (`H.member` icLocals ic) . fst) $ H.toList (icDependents ic)
  when (not (null errs)) $ do
    forM_ errs $ \(_, os) -> forM_ os $ \o ->
      reportAt o ELError "undefined variable"
    mzero

defcheckExpr :: [PBinder] -> SExpr -> ElabM (S.Set VarName)
defcheckExpr bis = defcheckExpr' where
  ctx = H.fromList (mapMaybe f bis) where
    f (PReg v (DepType _ vs)) = Just (v, vs)
    f _ = Nothing
  defcheckExpr' (SVar v) = return $
    maybe (S.singleton v) S.fromList (H.lookup v ctx)
  defcheckExpr' (App t es) = do
    (_, args, DepType _ rs) <- now >>= getTerm t
    (m, ev) <- defcheckArgs args es
    return (ev <> S.fromList ((m H.!) <$> rs))

  defcheckArgs :: [PBinder] -> [SExpr] ->
    ElabM (H.HashMap VarName VarName, S.Set VarName)
  defcheckArgs = \args es -> go args es H.empty S.empty where
    go [] [] m ev = return (m, ev)
    go (PBound x _ : args) (SVar v : es) m ev =
      go args es (H.insert x v m) ev
    go (PReg _ (DepType _ vs) : args) (e : es) m ev = do
      ev' <- defcheckExpr' e
      let ev2 = foldl' (\ev1 v -> S.delete (m H.! v) ev1) ev' vs
      go args es m (ev <> ev2)
    go _ _ _ _ = error "bad expr, should already have been caught"
