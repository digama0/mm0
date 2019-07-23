{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module MM0.Compiler.Elaborator (elaborate, ErrorLevel(..), ElabError(..)) where

import Control.Monad.State
import Control.Monad.RWS.Strict
import Data.List
import Data.Bits
import Data.Word8
import Data.Maybe
import Data.Default
import Data.Foldable
import qualified Data.HashMap.Strict as H
import qualified Data.Set as S
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Mutable.Dynamic as VD
import qualified Data.Sequence as Q
import qualified Data.Text as T
import MM0.Compiler.Parser (ParseError)
import MM0.Compiler.AST
import MM0.Compiler.Env
import MM0.Compiler.MathParser
import MM0.Compiler.PrettyPrinter
import MM0.Util

elaborate :: Bool -> [ParseError] -> AST -> IO ([ElabError], Env)
elaborate mm0 errs ast = do
  (_, errs', env) <- runElab (mapM_ elabStmt ast) mm0 (toElabError <$> errs) initialBindings
  return (errs', env)

elabStmt :: AtPos Stmt -> Elab ()
elabStmt (AtPos pos s) = resuming $ withTimeout pos $ case s of
  Sort px x sd -> addSort px x sd
  Decl vis dk px x bis ret v -> addDecl vis dk px x bis ret v
  Notation (Delimiter cs Nothing) -> lift $ addDelimiters cs cs
  Notation (Delimiter ls (Just rs)) -> lift $ addDelimiters ls rs
  Notation (Prefix px x tk prec) -> addPrefix px x tk prec
  Notation (Infix r px x tk prec) -> addInfix r px x tk prec
  Notation (NNotation px x bis _ lits) -> addNotation px x bis lits
  Notation (Coercion px x s1 s2) -> addCoercion px x s1 s2
  Do lvs -> do
    ifMM0 $ reportAt pos ELWarning "(MM0 mode) do block not supported"
    mapM_ evalToplevel lvs
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
  modifyInfer $ \ic -> ic {
    icDependents = foldl' (\m (AtPos i x) ->
      H.alter (Just . maybe [i] (i:)) x m) (icDependents ic) ts }

inferBinder :: Binder -> ElabM (Maybe (Offset, Local, InferResult))
inferBinder bi@(Binder o l oty) = case oty of
  Nothing -> do
    ifMM0 $ reportAt o ELWarning "(MM0 mode) missing type"
    Nothing <$ addVar True
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
    modifyInfer $ \ic -> ic {icLocals = locals'}

addDecl :: Visibility -> DeclKind -> Offset -> T.Text ->
  [Binder] -> Maybe [Type] -> Maybe AtLisp -> ElabM ()
addDecl vis dk px x bis ret v = do
  mm0 <- asks efMM0
  when (mm0 && vis /= VisDefault) $
    reportAt px ELWarning "(MM0 mode) visibility modifiers not supported"
  let (bis', ret') = unArrow bis ret
  decl <- withInfer $ do
    fmlas <- catMaybes <$> mapM inferBinder bis'
    decl <- case (dk, ret', v) of
      (DKDef, Just (TType ty), Nothing) -> do
        inferDepType ty
        if mm0 then do
          (pbs, hs, _) <- buildBinders px True bis' fmlas
          unless (null hs) $ error "impossible"
          return $ DDef vis pbs (unDepType ty) Nothing
        else do
          reportAt px ELWarning "definition has no body; axiomatizing"
          (pbs, hs, _) <- buildBinders px True bis' fmlas
          unless (null hs) $ error "impossible"
          return $ DTerm pbs (unDepType ty)
      (DKDef, _, Just (AtLisp _ (AFormula f))) -> do
        let ret'' = case ret' of Just (TType ty) -> Just ty; _ -> Nothing
        forM_ ret'' inferDepType
        IR _ v' s _ <- parseMath f >>=
          inferQExpr ((\(AtDepType s _) -> (unPos s, False)) <$> ret'')
        (pbs, hs, dums) <- buildBinders px True bis' fmlas
        unless (null hs) $ error "impossible"
        vs <- case ret'' of
          Just (AtDepType (AtPos o _) avs) -> do
            vs' <- defcheckExpr pbs v'
            let vs1 = unPos <$> avs
            let bad = foldr S.delete vs' vs1
            unless (S.null bad) $
              escapeAt o ("definition has undeclared free variable(s): " <>
                T.intercalate ", " (S.toList bad))
            return vs1
          Nothing -> do
            when mm0 $ reportAt px ELWarning "(MM0 mode) def has no return type"
            S.toList <$> defcheckExpr pbs v'
        return $ DDef vis pbs (DepType s vs) (Just (dums, v'))
      (DKDef, _, Just (AtLisp o _)) -> unimplementedAt o
      (DKTerm, Just (TType ty), _) -> do
        inferDepType ty
        (pbs, hs, _) <- buildBinders px False bis' fmlas
        unless (null hs) $ error "impossible"
        return (DTerm pbs (unDepType ty))
      (DKAxiom, Just (TFormula f), _) -> do
        IR _ eret _ _ <- parseMath f >>= inferQExprProv
        (pbs, hs, _) <- buildBinders px False bis' fmlas
        return $ DAxiom pbs ((\(_, _, h) -> h) <$> hs) eret
      (DKTheorem, Just (TFormula f), _) -> do
        IR _ eret _ _ <- parseMath f >>= inferQExprProv
        (pbs, hs, _) <- buildBinders px False bis' fmlas
        case v of
          Nothing ->
            if mm0 then
              return $ DTheorem vis pbs ((\(_, _, h) -> h) <$> hs) eret mzero
            else do
              reportAt px ELWarning "theorem proof missing"
              return $ DAxiom pbs ((\(_, _, h) -> h) <$> hs) eret
          Just lv -> do
            when mm0 $ reportAt px ELWarning "(MM0 mode) theorem proofs not accepted"
            fork <- forkElabM $ withTimeout px $
              withTC (H.fromList $ (\bi -> (binderName bi, bi)) <$> pbs) $ do
                forM_ hs $ \(o, on, e) -> forM_ on $ \n ->
                  addSubproof n (sExprToLisp o e) (Atom o n)
                elabLisp eret lv
            return $ DTheorem vis pbs ((\(_, _, h) -> h) <$> hs) eret fork
      _ -> unimplementedAt px
    checkVarRefs >> return decl
  ins <- gets eDecls >>= checkNew ELError px
    ("duplicate " <> T.pack (show dk) <> " declaration '" <> x <> "'")
    (\(_, i, _, _) -> i) x
  n <- next
  modify $ \env -> env {eDecls = ins (n, px, decl, Nothing)}

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

addDeclNota :: Offset -> T.Text -> Maybe DeclNota -> DeclNota -> ElabM ()
addDeclNota px x old new = do
  forM_ old $ \no -> do
    i <- getDeclNotaOffset no
    reportErr $ ElabError ELWarning px px
      ("term '" <> x <> "' already has a notation")
      [(i, i, "previously declared here")]
  modify $ \env -> env {eDecls =
    H.adjust (\(s, o, d, _) -> (s, o, d, Just new)) x (eDecls env)}

addPrefix :: Offset -> T.Text -> Const -> Prec -> ElabM ()
addPrefix px x c@(Const o tk) prec = do
  (_, bis, _, no) <- try (now >>= getTerm x) >>=
    fromJustAt px ("term '" <> x <> "' not declared")
  insertPrec c prec
  insertPrefixInfo c (PrefixInfo o x (mkLiterals (length bis) prec 0))
  addDeclNota px x no (NPrefix tk)

addInfix :: Bool -> Offset -> T.Text -> Const -> Prec -> ElabM ()
addInfix r px x c@(Const o tk) prec = do
  (_, bis, _, no) <- try (now >>= getTerm x) >>=
    fromJustAt px ("term '" <> x <> "' not declared")
  guardAt px ("'" <> x <> "' must be a binary operator") (length bis == 2)
  insertPrec c prec
  insertInfixInfo c (InfixInfo o x r)
  addDeclNota px x no (NInfix tk)

addNotation :: Offset -> T.Text -> [Binder] -> [AtPos Literal] -> ElabM ()
addNotation px x bis = \lits -> do
  (_, bis', _, no) <- try (now >>= getTerm x) >>=
    fromJustAt px ("term '" <> x <> "' not declared")
  unless (length bis == length bis') $
    escapeAt px ("term '" <> x <> "' has " <> T.pack (show (length bis')) <>
      " arguments, expected " <> T.pack (show (length bis)))
  (c@(Const _ tk), ti) <- processLits lits
  insertPrefixInfo c (PrefixInfo px x ti)
  addDeclNota px x no (NPrefix tk)
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
    Just (_, [PReg _ (DepType s1' [])], DepType s2' [], no)
      | s1 == s1' && s2 == s2' -> do
        addCoe (Coe1 px x) s1 s2
        addDeclNota px x no (NCoe s1 s2)
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
      returnVar s (isLCurly l) $ modifyInfer $ \ic -> ic {
        icLocals = H.insert t (LIOld bi (Just s)) (icLocals ic) }
    (_, Just (_, bis, DepType s _, _)) -> do
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
      returnVar s1 bd' $ when (bd1 /= bd') $ modifyInfer $ \ic -> ic {
        icLocals = H.insert t (LINew o1 bd' s1) (icLocals ic) }
    (Nothing, Nothing) -> do
      (s, bd) <- fromJustAt o "cannot infer type" tgt
      returnVar s bd $ modifyInfer $ \ic -> ic {
        icLocals = H.insert t (LINew o bd s) (icLocals ic) }
inferQExpr' _ (QUnquote (AtLisp o e)) = asSExpr <$> eval o def e >>= \case
  Nothing -> escapeAt o $ "invalid s-expr: " <> T.pack (show e)
  Just e'@(SVar v) -> gets (H.lookup v . icLocals . eInfer) >>= \case
    Just (LIOld (Binder _ l (Just (TType (AtDepType (AtPos _ s) _)))) _) ->
      return $ IR o e' s (isLCurly l)
    _ -> escapeAt o $ "unknown variable '" <> v <> "'"
  Just e'@(App t _) -> try (now >>= getTerm t) >>= \case
    Just (_, _, DepType s _, _) -> return $ IR o e' s False
    _ -> escapeAt o $ "unknown term constructor '" <> t <> "'"

inferQExprProv :: QExpr -> ElabM InferResult
inferQExprProv q = gets eProvableSorts >>= \case
  [s] -> inferQExpr (Just (s, False)) q
  _ -> do
    IR o e s _ <- inferQExpr Nothing q
    try (getCoeProv app1 s) >>= \case
      Just (s2, c) -> return (IR o (c e) s2 False)
      Nothing -> escapeAt o ("type error, expected provable sort, got " <> s)

buildBinders :: Offset -> Bool -> [Binder] -> [(Offset, Local, InferResult)] ->
  ElabM ([PBinder], [(Offset, Maybe VarName, SExpr)], [(Offset, VarName, Sort)])
buildBinders px dum bis fs = do
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
          Just v -> H.lookup v locals >>= \case
            LIOld (Binder _ _ (Just (TFormula _))) _ -> Nothing
            LIOld bi'@(Binder _ _ (Just (TType _))) _ -> Just (v, bi')
            LIOld bi'@(Binder _ _ Nothing) Nothing -> Just (v, bi')
            LIOld (Binder o l' Nothing) (Just t) ->
              Just (v, Binder o l' (Just (TType (AtDepType (AtPos o t) []))))
            LINew o bd s -> Just (v, newvar v o bd s)
      bisAdd = sortOn fst (mapMaybe f (H.toList locals)) where
        f (v, LINew o bd s) = Just (v, newvar v o bd s)
        f _ = Nothing
      bisNew = bisAdd ++ bis1 where
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
  ifMM0 $ unless (null bisAdd) $ reportAt px ELWarning $ render' $
    "(MM0 mode) missing binders:" <> ppGroupedBinders (snd <$> bisAdd)
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
    (_, args, DepType _ rs, _) <- now >>= getTerm t
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

-----------------------------
-- Lisp evaluation
-----------------------------

newtype LCtx = LCtx (H.HashMap T.Text LispVal)

instance Default LCtx where
  def = LCtx H.empty

lcInsert :: T.Text -> LispVal -> LCtx -> LCtx
lcInsert "_" _ ctx = ctx
lcInsert x v (LCtx ctx) = LCtx (H.insert x v ctx)

evalToplevel :: AtLisp -> ElabM ()
evalToplevel (AtLisp _ (AList (AtLisp o (AAtom "def") : es))) = do
  (AtPos o' x, v) <- evalDefine o def es
  unless (x == "_") $ lispDefine o' x v
evalToplevel (AtLisp o e) = evalAndPrint o e

evalAndPrint :: Offset -> LispAST -> ElabM ()
evalAndPrint o e = eval o def e >>= unRef >>= \case
  Undef -> return ()
  e' -> reportAt o ELInfo $ T.pack $ show e'

evalAt :: LCtx -> AtLisp -> ElabM LispVal
evalAt ctx (AtLisp o e) = eval o ctx e

eval :: Offset -> LCtx -> LispAST -> ElabM LispVal
eval o ctx (AAtom e) = evalAtom o ctx e
eval _ _ (AString s) = return (String s)
eval _ _ (ANumber n) = return (Number n)
eval _ _ (ABool b) = return (Bool b)
eval _ _ (AList []) = return (List [])
eval _ ctx (AList (AtLisp o e : es)) = evalApp o ctx e es
eval _ _ val@(ADottedList (AtLisp o _) _ _) =
  escapeAt o $ "attempted to evaluate an improper list: " <> T.pack (show val)
eval _ ctx (AFormula f) = parseMath f >>= evalQExpr ctx

evalList :: a -> (ElabM LispVal -> ElabM a -> ElabM a) -> LCtx -> [AtLisp] -> ElabM a
evalList a _ _ [] = return a
evalList a f ctx (AtLisp _ (AList (AtLisp o (AAtom "def") : ds)) : es) = do
  (AtPos _ x, v) <- evalDefine o ctx ds
  evalList a f (lcInsert x v ctx) es
evalList a f ctx (e : es) = f (evalAt ctx e) (evalList a f ctx es)

eval1 :: ElabM LispVal -> LCtx -> [AtLisp] -> ElabM LispVal
eval1 m ctx es =
  evalList Nothing (liftM2 $ \a b -> Just $ fromMaybe a b) ctx es >>= \case
    Nothing -> m
    Just a -> return a

evals :: LCtx -> [AtLisp] -> ElabM [LispVal]
evals = evalList [] $ liftM2 (:)

evalAtom :: Offset -> LCtx -> T.Text -> ElabM LispVal
evalAtom o _ v@"_" = return $ Atom o v
evalAtom o (LCtx ctx) v = case H.lookup v ctx of
  Just e -> return e
  Nothing -> try (lispLookupName v) >>= \case
    Just e -> return e
    Nothing -> escapeAt o $ "Reference to unbound variable '" <> v <> "'"

unRef :: LispVal -> ElabM LispVal
unRef (Ref e) = getRef e >>= unRef
unRef e = return e

call :: Offset -> T.Text -> [LispVal] -> ElabM LispVal
call o v es = try (lispLookupName v) >>= \case
  Just e -> unRef e >>= \case
    Proc f -> f o o es
    e' -> escapeAt o $ "not a function, cannot apply: " <> T.pack (show e')
  Nothing -> escapeAt o $ "Unknown function '" <> v <> "'"

evalApp :: Offset -> LCtx -> LispAST -> [AtLisp] -> ElabM LispVal
evalApp o ctx (AAtom e) es = evalAtom o ctx e >>= unRef >>= \case
  Syntax s -> evalSyntax o ctx s es
  Proc f -> evals ctx es >>= f o (o + T.length e)
  v -> escapeAt o $ "not a function, cannot apply: " <> T.pack (show v)
evalApp o ctx e es = eval o ctx e >>= unRef >>= \case
  Proc f -> evals ctx es >>= f o o
  v -> escapeAt o $ "not a function, cannot apply: " <> T.pack (show v)

evalSyntax :: Offset -> LCtx -> Syntax -> [AtLisp] -> ElabM LispVal
evalSyntax o _ Define _ = escapeAt o "def not permitted in expression context"
evalSyntax o _ Quote [] = escapeAt o "expected at least one argument"
evalSyntax _ ctx Quote (e : _) = quoteAt ctx e
evalSyntax _ ctx If (cond : t : es') = do
  cond' <- evalAt ctx cond
  if truthy cond' then evalAt ctx t else
    case es' of
      [] -> return Undef
      f : _ -> evalAt ctx f
evalSyntax o _ If _ = escapeAt o "expected at least two arguments"
evalSyntax _ ctx Lambda (vs : es@(_:_)) = do
  ls <- toLambdaSpec vs
  return (Proc (mkLambda ls ctx es))
evalSyntax o _ Lambda _ = escapeAt o "expected at least two arguments"
evalSyntax o ctx Begin es = eval1 (escapeAt o "expected at least one argument") ctx es
evalSyntax o ctx Focus es = Undef <$ focus o ctx es
evalSyntax o ctx Let es = do
  (xs, es') <- parseLet o es
  let go [] ctx' = eval1 (escapeAt o "expected at least two arguments") ctx' es'
      go ((AtPos _ x, v) : xs') ctx' = do
        v' <- evalAt ctx' v
        go xs' (lcInsert x v' ctx')
  go xs ctx
evalSyntax o ctx Letrec es = do
  (xs, es') <- parseLet o es
  ctx' <- go xs ctx (\_ -> return ())
  eval1 (escapeAt o "expected at least two arguments") ctx' es' where
  go :: [(AtPos Ident, AtLisp)] -> LCtx -> (LCtx -> ElabM ()) -> ElabM LCtx
  go [] ctx' f = ctx' <$ f ctx'
  go ((AtPos _ x, v) : xs) ctx' f = do
    a <- newRef Undef
    go xs (lcInsert x (Ref a) ctx') $
      \ctx2 -> f ctx2 >> evalAt ctx2 v >>= setRef a

data LambdaSpec = LSExactly [Ident] | LSAtLeast [Ident] Ident

toLambdaSpec :: AtLisp -> ElabM LambdaSpec
toLambdaSpec (AtLisp _ (AList es)) = LSExactly <$> mapM toIdent es
toLambdaSpec (AtLisp _ (ADottedList e1 es e2)) =
  liftM2 LSAtLeast (mapM toIdent (e1 : es)) (toIdent e2)
toLambdaSpec e = LSAtLeast [] <$> toIdent e

mkCtx :: Offset -> LambdaSpec -> [LispVal] -> LCtx -> ElabM LCtx
mkCtx o (LSExactly xs') = \vs -> mkCtxList xs' vs 0 where
  mkCtxList [] [] _ ctx = return ctx
  mkCtxList (x:xs) (v:vs) n ctx =
    mkCtxList xs vs (n+1) (lcInsert x v ctx)
  mkCtxList [] vs n _ = escapeAt o $
    "expected " <> T.pack (show n) <> " arguments, got " <> T.pack (show (n + length vs))
  mkCtxList xs [] n _ = escapeAt o $
    "expected " <> T.pack (show (n + length xs)) <> " arguments, got " <> T.pack (show n)
mkCtx o (LSAtLeast xs' r) = \vs -> mkCtxImproper xs' vs 0 where
  mkCtxImproper [] vs _ ctx =
    return (lcInsert r (List vs) ctx)
  mkCtxImproper (x:xs) (v:vs) n ctx =
    mkCtxImproper xs vs (n+1) (lcInsert x v ctx)
  mkCtxImproper xs [] n _ = escapeAt o $
    "expected at least " <> T.pack (show (n + length xs)) <> " arguments, got " <> T.pack (show n)

mkLambda :: LambdaSpec -> LCtx -> [AtLisp] -> Proc
mkLambda ls ctx es o _ vs = do
  ctx' <- mkCtx o ls vs ctx
  eval1 (escapeAt o "expected at least two arguments") ctx' es

evalDefine :: Offset -> LCtx -> [AtLisp] -> ElabM (AtPos Ident, LispVal)
evalDefine o' ctx (AtLisp o (AAtom x) : es) = do
  v <- eval1 (escapeAt o' "expected at least two arguments") ctx es
  return (AtPos o x, v)
evalDefine _ ctx (AtLisp _ (AList (AtLisp o (AAtom x) : xs)) : es) = do
  xs' <- mapM toIdent xs
  return (AtPos o x, Proc $ mkLambda (LSExactly xs') ctx es)
evalDefine _ ctx (AtLisp _ (ADottedList (AtLisp o (AAtom x)) xs r) : es) = do
  xs' <- mapM toIdent xs
  r' <- toIdent r
  return (AtPos o x, Proc $ mkLambda (LSAtLeast xs' r') ctx es)
evalDefine o _ _ = escapeAt o "def: syntax error"

toIdent :: AtLisp -> ElabM Ident
toIdent (AtLisp _ (AAtom x)) = return x
toIdent (AtLisp o _) = escapeAt o "expected an identifier"

parseLet :: Offset -> [AtLisp] -> ElabM ([(AtPos Ident, AtLisp)], [AtLisp])
parseLet _ (AtLisp o vs : es@(_:_)) = case vs of
  AList ls -> do
    xs <- mapM parseLetVar ls
    return (xs, es)
  _ -> escapeAt o "invalid syntax"
parseLet o _ = escapeAt o "expected at least two arguments"

parseLetVar :: AtLisp -> ElabM (AtPos Ident, AtLisp)
parseLetVar (AtLisp _ (AList [AtLisp o (AAtom x), e])) = return (AtPos o x, e)
parseLetVar (AtLisp o _) = escapeAt o "invalid syntax"

quoteAt :: LCtx -> AtLisp -> ElabM LispVal
quoteAt ctx (AtLisp o e) = quote o ctx e

quote :: Offset -> LCtx -> LispAST -> ElabM LispVal
quote o _ (AAtom e) = return $ Atom o e
quote _ ctx (AList [AtLisp _ (AAtom "unquote"), e]) = evalAt ctx e
quote _ ctx (AList es) = List <$> mapM (quoteAt ctx) es
quote _ ctx (ADottedList l es r) =
  liftM3 DottedList (quoteAt ctx l) (mapM (quoteAt ctx) es) (quoteAt ctx r)
quote _ _ (AString s) = return $ String s
quote _ _ (ANumber n) = return $ Number n
quote _ _ (ABool b) = return $ Bool b
quote _ _ (AFormula (Formula o f)) = return $ UnparsedFormula o f

asString :: Offset -> LispVal -> ElabM T.Text
asString _ (String s) = return s
asString o e = escapeAt o $ "expected a string, got " <> T.pack (show e)

asInt :: Offset -> LispVal -> ElabM Integer
asInt _ (Number n) = return n
asInt o e = escapeAt o $ "expected an integer, got " <> T.pack (show e)

goalType :: Offset -> LispVal -> ElabM LispVal
goalType _ (Goal _ ty) = return ty
goalType o e = escapeAt o $ "expected a goal, got " <> T.pack (show e)

sExprSubst :: Offset -> H.HashMap VarName LispVal -> SExpr -> LispVal
sExprSubst o m = go where
  go (SVar v) = m H.! v
  go (App t es) = List (Atom o t : (go <$> es))

inferType :: Offset -> LispVal -> ElabM LispVal
inferType _ (Goal _ ty) = return ty
inferType o (Atom _ h) = try (getSubproof h) >>= \case
  Just v -> return v
  Nothing -> escapeAt o $ "unknown hypothesis '" <> h <> "'"
inferType o (List (Atom _ t : es)) = try (now >>= getThm t) >>= \case
  Nothing -> escapeAt o $ "unknown theorem '" <> t <> "'"
  Just (_, bis, _, ret) ->
    let
      inferBis :: [PBinder] -> [LispVal] ->
        H.HashMap VarName LispVal -> ElabM LispVal
      inferBis (_ : _) [] _ = escapeAt o "not enough arguments"
      inferBis (bi : bis') (e : es') m = do
        inferBis bis' es' (H.insert (binderName bi) e m)
      inferBis [] _ m = return $ sExprSubst o m ret
    in inferBis bis es H.empty
inferType o (Ref g) = getRef g >>= inferType o
inferType o e = escapeAt o $ "not a proof: " <> T.pack (show e)

asSExpr :: LispVal -> Maybe SExpr
asSExpr (List (Atom _ t : ts)) = App t <$> mapM asSExpr ts
asSExpr (Atom _ x) = return $ SVar x
asSExpr _ = Nothing

asRef :: Offset -> LispVal -> ElabM (TVar LispVal)
asRef _ (Ref a) = return a
asRef o e = escapeAt o $ "not a ref-cell: " <> T.pack (show e)

unary :: Offset -> [LispVal] -> ElabM LispVal
unary _ [e] = return e
unary o es = escapeAt o $ "expected one argument, got " <> T.pack (show (length es))

evalFold1 :: Offset -> (a -> a -> a) -> [a] -> ElabM a
evalFold1 o _ [] = escapeAt o "expected at least one argument"
evalFold1 _ f es = return (foldl1 f es)

intBoolBinopProc :: (Integer -> Integer -> Bool) -> Proc
intBoolBinopProc f o _ es = mapM (asInt o) es >>= \case
    e : es'@(_:_) -> return $ Bool $ go e es'
    _ -> escapeAt o "expected at least two arguments"
  where
  go :: Integer -> [Integer] -> Bool
  go _ [] = True
  go e1 (e2 : es') = f e1 e2 && go e2 es'

truthy :: LispVal -> Bool
truthy (Bool False) = False
truthy _ = True

isPair :: LispVal -> Bool
isPair (DottedList _ _ _) = True
isPair (List (_:_)) = True
isPair _ = False

isNull :: LispVal -> Bool
isNull (List []) = True
isNull _ = False

isString :: LispVal -> Bool
isString (String _) = True
isString _ = False

isRef :: LispVal -> Bool
isRef (Ref _) = True
isRef _ = False

lispHd :: Offset -> LispVal -> ElabM LispVal
lispHd o (List []) = escapeAt o "evaluating 'hd ()'"
lispHd _ (List (e:_)) = return e
lispHd _ (DottedList e _ _) = return e
lispHd o _ = escapeAt o "expected a list"

lispTl :: Offset -> LispVal -> ElabM LispVal
lispTl o (List []) = escapeAt o "evaluating 'tl ()'"
lispTl _ (List (_:es)) = return (List es)
lispTl _ (DottedList _ [] e) = return e
lispTl _ (DottedList _ (e:es) t) = return (DottedList e es t)
lispTl o _ = escapeAt o "expected a list"

initialBindings :: [(T.Text, LispVal)]
initialBindings = [
  ("def", Syntax Define), ("quote", Syntax Quote),
  ("fn", Syntax Lambda), ("if", Syntax If), ("begin", Syntax Begin),
  ("let", Syntax Let), ("letrec", Syntax Letrec),
  ("focus", Syntax Focus) ] ++
  (mapSnd Proc <$> initialProcs) where

  initialProcs :: [(T.Text, Proc)]
  initialProcs = [
    ("display", \o o' es ->
      unary o es >>= asString o >>= reportSpan o o' ELInfo >> pure Undef),
    ("print", \o o' es -> unary o es >>= \e -> do
      reportSpan o o' ELInfo $! T.pack (show e)
      pure Undef),
    ("apply", \o o' -> \case
      Proc proc : e : es ->
        let args (List es') [] = return es'
            args e' [] = escapeAt o $ "not a list: " <> T.pack (show e')
            args e' (e2 : es') = (e':) <$> args e2 es'
        in args e es >>= proc o o'
      e : _ : _ -> escapeAt o $ "not a procedure: " <> T.pack (show e)
      _ -> escapeAt o "expected at least two arguments"),
    ("+", \o _ es -> Number . sum <$> mapM (asInt o) es),
    ("*", \o _ es -> Number . product <$> mapM (asInt o) es),
    ("max", \o _ es ->
      mapM (asInt o) es >>= evalFold1 o max >>= return . Number),
    ("min", \o _ es ->
      mapM (asInt o) es >>= evalFold1 o min >>= return . Number),
    ("-", \o _ es -> mapM (asInt o) es >>= \case
      [] -> escapeAt o "expected at least one argument"
      [n] -> return $ Number (-n)
      n : ns -> return $ Number (n - sum ns)),
    ("<", intBoolBinopProc (<)),
    ("<=", intBoolBinopProc (<=)),
    (">", intBoolBinopProc (>)),
    (">=", intBoolBinopProc (>=)),
    ("=", intBoolBinopProc (==)),
    ("->string", \o _ es -> unary o es >>= \case
      Number n -> return $ String $ T.pack $ show n
      String s -> return $ String s
      Atom _ s -> return $ String s
      UnparsedFormula _ s -> return $ String s
      e -> return $ String $ T.pack $ show e),
    ("string->atom", \o _ es -> unary o es >>= asString o >>= return . Atom o),
    ("not", \o _ es -> Bool . not . truthy <$> unary o es),
    ("and", \_ _ es -> return $ Bool $ all truthy es),
    ("or", \_ _ es -> return $ Bool $ any truthy es),
    ("list", \_ _ -> return . List),
    ("cons", \_ _ -> \case
      [] -> return $ List []
      es' -> return $ foldl1 cons es'),
    ("pair?", \o _ es -> Bool . isPair <$> unary o es),
    ("null?", \o _ es -> Bool . isNull <$> unary o es),
    ("string?", \o _ es -> Bool . isString <$> unary o es),
    ("hd", \o _ es -> unary o es >>= lispHd o),
    ("tl", \o _ es -> unary o es >>= lispTl o),
    ("ref?", \o _ es -> Bool . isRef <$> unary o es),
    ("ref!", \_ _ -> \case
      [] -> Ref <$> newRef Undef
      e:_ -> Ref <$> newRef e),
    ("get!", \o _ es -> unary o es >>= asRef o >>= getRef),
    ("set!", \o _ -> \case
      [e, v] -> asRef o e >>= \x -> Undef <$ setRef x v
      _ -> escapeAt o "expected two arguments"),

    -- MM0 specific
    ("set-timeout", \o _ es -> unary o es >>= asInt o >>= \n ->
      Undef <$ modify (\env -> env {eTimeout = 1000 * fromInteger n})),
    ("mvar?", \o _ es -> Bool . isMVar <$> unary o es),
    ("goal?", \o _ es -> Bool . isGoal <$> unary o es),
    ("mvar!", \o _ -> \case
      [Atom _ s, Bool bd] -> Ref <$> newMVar o s bd
      _ -> escapeAt o "invalid arguments"),
    ("pp", \o _ es -> unary o es >>= ppExpr >>= return . String . render),
    ("goal", \o _ es -> Goal o <$> unary o es),
    ("goal-type", \o _ es -> unary o es >>= unRef >>= goalType o),
    ("infer-type", \o _ es -> unary o es >>= inferType o),
    ("get-goals", \_ _ _ -> List . fmap Ref . V.toList . tcGoals <$> getTC),
    ("set-goals", \o _ es -> Undef <$ (mapM (asRef o) es >>= setGoals)),
    ("to-expr", \o _ es -> unary o es >>= parseRefine o >>= toExpr "" False),
    ("refine", \o _ es -> Undef <$ refine o es),
    ("have", \o _ -> \case
      [Atom _ x, e] -> do
        ty <- Ref <$> newUnknownMVar o
        p <- withGoals o $ \gv -> parseRefine o e >>= refineProof gv ty
        Undef <$ addSubproof x ty p
      [Atom _ x, ty', e] -> do
        ty <- parseRefine o ty' >>= toExpr "" False
        p <- withGoals o $ \gv -> parseRefine o e >>= refineProof gv ty
        Undef <$ addSubproof x ty p
      _ -> escapeAt o "invalid arguments"),
    ("stat", \o o' _ ->
      getStat >>= reportSpan o o' ELInfo . render >> pure Undef),

    -- redefinable configuration functions
    ("refine-extra-args", \o _ -> \case
      [_, e] -> return e
      _:e:_ -> e <$ reportAt o ELError "too many arguments"
      _ -> escapeAt o "expected at least two arguments")]

evalQExpr :: LCtx -> QExpr -> ElabM LispVal
evalQExpr ctx (QApp (AtPos o e) es) =
  List . (Atom o e :) <$> mapM (evalQExpr ctx) es
evalQExpr ctx (QUnquote (AtLisp o e)) = eval o ctx e

-----------------------------
-- Tactics
-----------------------------

tryRefine :: Offset -> LispVal -> ElabM ()
tryRefine _ Undef = return ()
tryRefine o e = refine o [e]

evalRefines :: Offset -> LCtx -> [AtLisp] -> ElabM ()
evalRefines o = evalList () (\e l -> e >>= tryRefine o >> l)

elabLisp :: SExpr -> AtLisp -> ElabM Proof
elabLisp t e@(AtLisp o _) = do
  g <- newRef (Goal o (sExprToLisp o t))
  modifyTC $ \tc -> tc {tcGoals = V.singleton g}
  evalAt def e >>= tryRefine o
  gs' <- tcGoals <$> getTC
  forM_ gs' $ \g' -> getRef g' >>= \case
    Goal o' ty -> do
      pp <- ppExpr ty
      reportAt o' ELError $ render' $ "|-" <+> doc pp
    _ -> return ()
  unless (V.null gs') mzero
  cleanProof o (Ref g)

cleanProof :: Offset -> LispVal -> ElabM Proof
cleanProof o (Ref g) = getRef g >>= \case
  Goal o' ty -> do
    pp <- ppExpr ty
    escapeAt o' $ render' $ "??? |-" <+> doc pp
  e -> cleanProof o e
cleanProof _ (Atom _ h) = return $ ProofHyp h
cleanProof o (List [Atom _ ":unfold", ty, List xs, es]) =
  liftM3 ProofUnfold (cleanTerm o ty) (mapM (cleanVar o) xs) (cleanProof o es)
cleanProof o (List (Atom _ t : es)) = try (now >>= getThm t) >>= \case
  Nothing -> escapeAt o $ "unknown theorem '" <> t <> "'"
  Just (_, bis, _, _) ->
    let (es1, es2) = splitAt (length bis) es in
    liftM2 (ProofThm t) (mapM (cleanTerm o) es1) (mapM (cleanProof o) es2)
cleanProof o e = escapeAt o $ "bad proof: " <> T.pack (show e)

cleanTerm :: Offset -> LispVal -> ElabM SExpr
cleanTerm o (Ref g) = getRef g >>= \case
  MVar n o' s bd -> escapeAt o' $ render $ ppMVar n s bd
  e -> cleanTerm o e
cleanTerm _ (Atom _ x) = return $ SVar x
cleanTerm o (List (Atom _ t : es)) = App t <$> mapM (cleanTerm o) es
cleanTerm o e = escapeAt o $ "bad term: " <> T.pack (show e)

cleanVar :: Offset -> LispVal -> ElabM VarName
cleanVar o (Ref g) = getRef g >>= \case
  MVar n o' s bd -> escapeAt o' $ render $ ppMVar n s bd
  e -> cleanVar o e
cleanVar _ (Atom _ x) = return x
cleanVar o e = escapeAt o $ "bad var: " <> T.pack (show e)

data InferMode = IMRegular | IMExplicit | IMBoundOnly deriving (Eq, Show)

imPopBd :: InferMode -> Bool -> Bool
imPopBd IMRegular _ = False
imPopBd IMExplicit _ = True
imPopBd IMBoundOnly bd = bd

data RefineExpr =
    RAtom Offset T.Text
  | RApp InferMode Offset T.Text [RefineExpr]
  | RExact Offset LispVal
  deriving (Show)

reOffset :: RefineExpr -> Offset
reOffset (RAtom o _) = o
reOffset (RApp _ o _ _) = o
reOffset (RExact o _) = o

unconsIf :: Bool -> a -> [a] -> (a, [a])
unconsIf False a es = (a, es)
unconsIf True a [] = (a, [])
unconsIf True _ (e : es) = (e, es)

asAtom :: Offset -> LispVal -> ElabM (Offset, T.Text)
asAtom _ (Atom o t) = return (o, t)
asAtom o _ = escapeAt o "expected an 'atom"

parseRefine :: Offset -> LispVal -> ElabM RefineExpr
parseRefine _ (Atom o x) = return (RAtom o x)
parseRefine o (List []) = return (RAtom o "_")
parseRefine _ (List [Atom o "!"]) = escapeAt o "expected at least one argument"
parseRefine _ (List (Atom o "!" : t : es)) =
  asAtom o t >>= \(o', t') -> RApp IMExplicit o' t' <$> mapM (parseRefine o') es
parseRefine _ (List [Atom o "!!"]) =
  escapeAt o "expected at least one argument"
parseRefine _ (List (Atom o "!!" : t : es)) =
  asAtom o t >>= \(o', t') -> RApp IMBoundOnly o' t' <$> mapM (parseRefine o') es
parseRefine _ (List [Atom o ":verb", e]) = return $ RExact o e
parseRefine o (List (t : es)) =
  asAtom o t >>= \(o', t') -> RApp IMRegular o' t' <$> mapM (parseRefine o') es
parseRefine o (UnparsedFormula o' f) =
  parseMath (Formula o' f) >>= evalQExpr def >>= parseRefine o
parseRefine o e = escapeAt o $ "syntax error in parseRefine: " <> T.pack (show e)

data UnifyResult = UnifyOK | UnifyUnfold (Q.Seq LispVal)

instance Semigroup UnifyResult where
  UnifyOK <> u = u
  u <> UnifyOK = u
  UnifyUnfold s1 <> UnifyUnfold s2 = UnifyUnfold (s1 <> s2)
instance Monoid UnifyResult where mempty = UnifyOK

coerceTo :: Offset -> LispVal -> LispVal -> LispVal -> ElabM LispVal
coerceTo o tgt p ty = unifyAt o tgt ty >>= \case
    UnifyOK -> return p
    UnifyUnfold xs -> return (List [Atom o ":unfold", ty, List (toList xs), p])

coerceTo' :: Offset -> LispVal -> LispVal -> ElabM LispVal
coerceTo' o tgt p = inferType o p >>= coerceTo o tgt p

unifyAt :: Offset -> LispVal -> LispVal -> ElabM UnifyResult
unifyAt o e1 e2 = try (unify o e1 e2) >>= \case
    Just u -> return u
    Nothing -> unifyErr e1 e2 >>= reportAt o ELError . render >> return mempty

unify :: Offset -> LispVal -> LispVal -> ElabM UnifyResult
unify o (Ref g) v = assign o g v
unify o v (Ref g) = assign o g v
unify o (Atom _ x) (Atom _ y) = do
  unless (x == y) $ escapeAt o $
    "variables do not match: " <> x <> " != " <> y
  return UnifyOK
unify o v1@(List (Atom _ t1 : es1)) v2@(List (Atom _ t2 : es2)) =
  if t1 == t2 then go es1 es2 else do
    decls <- gets eDecls
    case (H.lookup t1 decls, H.lookup t2 decls) of
      (Just (n1, _, _, _), Just (n2, _, DDef _ args2 _ (Just (ds2, val2)), _))
        | n1 < n2 -> unfold o args2 ds2 val2 es2 v1
      (Just (_, _, DDef _ args1 _ (Just (ds1, val1)), _), _) -> unfold o args1 ds1 val1 es1 v2
      (_, Just (_, _, DDef _ args2 _ (Just (ds2, val2)), _)) -> unfold o args2 ds2 val2 es2 v1
      _ -> escapeAt o $ "terms do not match: " <> t1 <> " != " <> t2
  where
  go [] [] = return mempty
  go (e1 : es1') (e2 : es2') = liftM2 (<>) (unify o e1 e2) (go es1' es2')
  go _ _ = escapeAt o $ "bad terms: " <> T.pack (show (t1, length es1, t2, length es2))
unify o (Atom _ v) e2@(List (Atom _ _ : _)) = do
  pp <- ppExpr e2
  escapeAt o $ "variable vs term: " <> v <> " != " <> render pp
unify o e1@(List (Atom _ _ : _)) (Atom _ v) = do
  pp <- ppExpr e1
  escapeAt o $ "term vs variable: " <> render pp <> " != " <> v
unify o e1 e2 = escapeAt o $ "bad terms: " <> T.pack (show (e1, e2))

assign :: Offset -> TVar LispVal -> LispVal -> ElabM UnifyResult
assign o g = \v -> getRef g >>= \case
  MVar _ _ _ _ -> go v
  v' -> unify o v v'
  where
  go (Ref g') | g == g' = return mempty
  go v@(Ref g') = getRef g' >>= \case
    v'@(Ref _) -> go v'
    _ -> check v
  go v = check v
  check v = try (occursCheck g v) >>= \case
    Just v' -> mempty <$ setRef g v'
    Nothing -> escapeAt o "occurs-check failed, can't build infinite assignment"

occursCheck :: TVar LispVal -> LispVal -> ElabM LispVal
occursCheck g (Ref g') | g == g' = mzero
occursCheck g e@(Ref g') = getRef g' >>= \case
  MVar _ _ _ _ -> return e
  e' -> occursCheck g e'
occursCheck g (List (t : es)) = List . (t :) <$> mapM (occursCheck g) es
occursCheck _ e = return e

unfold :: Offset -> [PBinder] -> [(Offset, VarName, Sort)] ->
  SExpr -> [LispVal] -> LispVal -> ElabM UnifyResult
unfold o bis ds val es e2 = buildSubst bis es H.empty where

  buildSubst :: [PBinder] -> [LispVal] -> H.HashMap VarName LispVal -> ElabM UnifyResult
  buildSubst (bi : bis') (e : es') m =
    buildSubst bis' es' (H.insert (binderName bi) e m)
  buildSubst [] [] m = buildDummies ds Q.empty m
  buildSubst _ _ _ = escapeAt o "incorrect arguments"

  buildDummies :: [(Offset, VarName, Sort)] -> Q.Seq LispVal ->
    H.HashMap VarName LispVal -> ElabM UnifyResult
  buildDummies ((_, x, s) : ds') q m = do
    v <- Ref <$> newMVar o s True
    buildDummies ds' (q Q.|> v) (H.insert x v m)
  buildDummies [] q m = (UnifyUnfold q <>) <$> unify o (sExprSubst o m val) e2

toExpr :: Sort -> Bool -> RefineExpr -> ElabM LispVal
toExpr _ _ (RExact _ e) = return e -- TODO: check type
toExpr s bd (RAtom o "_") = Ref <$> newMVar o s bd
toExpr s bd (RAtom o x) = do
  H.lookup x . tcVars <$> getTC >>= \case
    Just (PBound _ s') -> do
      unless (s == s') $ reportAt o ELError "variable has the wrong sort"
    Just (PReg _ (DepType s' _)) -> do
      unless (s == s') $ reportAt o ELError "variable has the wrong sort"
      when bd $ reportAt o ELError "expected a bound variable"
    Nothing -> modifyTC $ \tc -> tc {tcVars = H.insert x (PBound x s) (tcVars tc)}
  return $ Atom o x
toExpr s bd (RApp _ o t es) = try (now >>= getTerm t) >>= \case
  Nothing -> if null es then toExpr s bd (RAtom o t) else
    escapeAt o $ "unknown term '" <> t <> "'"
  Just (_, bis, ret, _) -> do
    let
      refineBis :: [PBinder] -> [RefineExpr] -> ElabM [LispVal]
      refineBis (bi : bis') rs =
        let (r, rs') = unconsIf True (RAtom o "_") rs in
        liftM2 (:)
          (toExpr (dSort $ binderType bi) (binderBound bi) r)
          (refineBis bis' rs')
      refineBis [] [] = return []
      refineBis [] (r:_) = [] <$ reportAt (reOffset r) ELError "too many arguments"
    es' <- refineBis bis es
    unless (s == dSort ret) $ reportAt o ELError $
      "type error: expected " <> s <> ", got " <> dSort ret
    when bd $ reportAt o ELError "expected a bound variable"
    return $ List $ Atom o t : es'

getGoals :: Offset -> ElabM [TVar LispVal]
getGoals o = try getTC >>= \case
  Just tc -> return $ V.toList $ tcGoals tc
  Nothing -> escapeAt o "not in a theorem context"

withGoals :: Offset -> (VD.IOVector (TVar LispVal) -> ElabM a) -> ElabM a
withGoals o m = do
  gv <- VD.new 0
  a <- m gv
  v <- VD.unsafeFreeze gv
  gs <- getGoals o
  setGoals (V.toList v ++ gs)
  return a

newGoal :: VD.IOVector (TVar LispVal) -> Offset -> LispVal -> ElabM (TVar LispVal)
newGoal gv o ty = do
  g <- newRef (Goal o ty)
  liftIO $ VD.pushBack gv g
  return g

refine :: Offset -> [LispVal] -> ElabM ()
refine o es = do
  withGoals o $ \gv -> do
    gs <- getGoals o
    let go :: [LispVal] -> [TVar LispVal] -> ElabM ()
        go [] gs' = setGoals gs'
        go _ [] = setGoals []
        go es1@(e:es') (g:gs') = do
          getRef g >>= \case
            Goal _ ty -> do
              parseRefine o e >>= refineProof gv ty >>= setRef g
              go es' gs'
            _ -> go es1 gs'
    go es gs
  cleanMVars

refineProof :: VD.IOVector (TVar LispVal) ->
  LispVal -> RefineExpr -> ElabM LispVal
refineProof gv = refinePf where
  refinePf :: LispVal -> RefineExpr -> ElabM LispVal
  refinePf ty (RExact o e) = coerceTo' o ty e
  refinePf ty (RAtom o "_") = Ref <$> newGoal gv o ty
  refinePf ty (RAtom o h) = try (getSubproof h) >>= \case
    Just v -> coerceTo o ty (Atom o h) v
    Nothing -> try (now >>= getThm h) >>= \case
      Just (_, bis, hs, ret) -> refinePfThm ty IMRegular o h [] bis hs ret
      Nothing -> escapeAt o $ "unknown hypothesis '" <> h <> "'"
  refinePf ty (RApp _ o "_" []) = Ref <$> newGoal gv o ty
  refinePf ty (RApp _ o "_" es) = do
    mv <- Ref <$> newUnknownMVar o
    Ref <$> newGoal gv o mv >>= refineExtraArgs o mv ty es
  refinePf ty (RApp im o t es) = try (now >>= getThm t) >>= \case
    Just (_, bis, hs, ret) -> refinePfThm ty im o t es bis hs ret
    Nothing -> try (getSubproof t) >>= \case
      Just v -> refineExtraArgs o v ty es (Atom o t)
      _ -> escapeAt o $ "unknown theorem '" <> t <> "'"

  refinePfThm :: LispVal -> InferMode -> Offset -> T.Text -> [RefineExpr] ->
    [PBinder] -> [SExpr] -> SExpr -> ElabM LispVal
  refinePfThm ty im o t es bis hs ret = refineBis bis es id H.empty where
    refineBis :: [PBinder] -> [RefineExpr] -> ([LispVal] -> [LispVal]) ->
      H.HashMap VarName LispVal -> ElabM LispVal
    refineBis (bi : bis') rs f m = do
      let bd = binderBound bi
          (r, rs') = unconsIf (imPopBd im bd) (RAtom o "_") rs
      e <- toExpr (dSort $ binderType bi) bd r
      refineBis bis' rs' (f . (e :)) (H.insert (binderName bi) e m)
    refineBis [] rs f m = refineHs hs rs f m

    refineHs :: [SExpr] -> [RefineExpr] -> ([LispVal] -> [LispVal]) ->
      H.HashMap VarName LispVal -> ElabM LispVal
    refineHs (e : es') rs f m = do
      let (r, rs') = unconsIf True (RAtom o "_") rs
      p <- refinePf (sExprSubst o m e) r
      refineHs es' rs' (f . (p :)) m
    refineHs [] rs f m =
      refineExtraArgs o (sExprSubst o m ret) ty rs (List (Atom o t : f []))

  refineExtraArgs :: Offset -> LispVal -> LispVal -> [RefineExpr] -> LispVal -> ElabM LispVal
  refineExtraArgs o v ty [] e = coerceTo o ty e v
  refineExtraArgs o _ ty rs@(r:_) e = do
    es <- forM rs $ \r' -> do
      mv <- newUnknownMVar o
      refinePf (Ref mv) r'
    e' <- call (reOffset r) "refine-extra-args" $ Proc callback : e : es
    coerceTo' o ty e'
    where
    callback o' _ [ty', e'] = parseRefine o' e' >>= refinePf ty'
    callback o' _ [e'] = do
      mv <- newUnknownMVar o'
      parseRefine o' e' >>= refinePf (Ref mv)
    callback o' _ _ = escapeAt o' "expected two arguments"

focus :: Offset -> LCtx -> [AtLisp] -> ElabM ()
focus o ctx es = getGoals o >>= \case
  [] -> escapeAt o "no goals"
  g1 : gt -> do
    setGoals [g1]
    evalRefines o ctx es
    gs' <- getGoals o
    setGoals $ gs' ++ gt
