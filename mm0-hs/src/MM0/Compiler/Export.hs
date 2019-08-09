module MM0.Compiler.Export where

import Control.Monad.State
import qualified Data.Map.Strict as M
import qualified Data.HashMap.Strict as H
import qualified Data.Text as T
import MM0.Compiler.Env

export :: ElabM ()
export = do
  m <- collectDecls
  undefined m

isPublic :: Decl -> Bool
isPublic (DTerm _ _) = True
isPublic (DAxiom _ _ _) = True
isPublic (DDef vis _ _ _) = vis /= Local
isPublic (DTheorem vis _ _ _ _) = vis == Public

type DeclMap = M.Map SeqNum (Either Sort Ident)
collectDecls :: ElabM DeclMap
collectDecls = do
  env <- get
  m <- processDecls (H.toList (eDecls env)) M.empty
  return (H.foldlWithKey' (\m' x (s, _, _) -> M.insert s (Left x) m') m (eSorts env))
  where

  processDecls :: [(Ident, (SeqNum, (Range, Range), Decl, b))] -> DeclMap -> ElabM DeclMap
  processDecls ((x, (s, (_, o), d, _)) : ds) m | isPublic d && not (M.member s m) =
    execStateT (checkDecl' o s d) (M.insert s (Right x) m) >>= processDecls ds
  processDecls (_ : ds) m = processDecls ds m
  processDecls [] m = return m

  checkDecl' :: Range -> SeqNum -> Decl -> StateT DeclMap ElabM ()
  checkDecl' _ _ (DTerm _ _) = return ()
  checkDecl' o s (DAxiom _ hs ret) = mapM_ (checkSExpr o s) hs >> checkSExpr o s ret
  checkDecl' _ _ (DDef _ _ _ Nothing) = return ()
  checkDecl' o s (DDef _ _ _ (Just (_, e))) = checkSExpr o s e
  checkDecl' o s (DTheorem _ _ hs ret pr) = do
    mapM_ (checkSExpr o s . snd) hs
    checkSExpr o s ret
    lift pr >>= checkProof o s

  checkDecl :: Range -> SeqNum -> Ident -> StateT DeclMap ElabM ()
  checkDecl o s x = lift (gets (H.lookup x . eDecls)) >>= \case
    Just (s', (_, o'), d, _) -> do
      unless (s' < s) $ lift $ reportSpan o ELError $ T.pack (show x) <> " is forward-referenced"
      m <- get
      unless (M.member s' m) $ modify (M.insert s' (Right x)) >> checkDecl' o' s' d
    Nothing -> lift $ reportSpan o ELError $ "unknown declaration " <> T.pack (show x)

  checkSExpr :: Range -> SeqNum -> SExpr -> StateT DeclMap ElabM ()
  checkSExpr _ _ (SVar _) = return ()
  checkSExpr o s (App t es) = checkDecl o s t >> mapM_ (checkSExpr o s) es

  checkProof :: Range -> SeqNum -> Proof -> StateT DeclMap ElabM ()
  checkProof _ _ (ProofHyp _) = return ()
  checkProof o s (ProofThm t es ps) =
    checkDecl o s t >> mapM_ (checkSExpr o s) es >> mapM_ (checkProof o s) ps
  checkProof o s (ProofConv _ c p) = checkConv o s c >> checkProof o s p
  checkProof o s (ProofLet _ p1 p2) = checkProof o s p1 >> checkProof o s p2

  checkConv :: Range -> SeqNum -> Conv -> StateT DeclMap ElabM ()
  checkConv _ _ (CVar _) = return ()
  checkConv o s (CApp t cs) = checkDecl o s t >> mapM_ (checkConv o s) cs
  checkConv o s (CSym c) = checkConv o s c
  checkConv o s (CUnfold t es _ c) =
    checkDecl o s t >> mapM_ (checkSExpr o s) es >> checkConv o s c
