module SpecCheck(insertSort, insertDecl, insertSpec) where

import Control.Monad.State.Class
import Control.Monad.RWS.Strict
import Control.Monad.Except
import Data.Maybe
import Data.List
import Debug.Trace
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Sequence as Q
import AST
import Environment
import ParserEnv
import LocalContext
import Util

insertSort :: Ident -> SortData -> Environment -> Either String Environment
insertSort v sd e = do
  s' <- insertNew ("sort " ++ v ++ " already declared") v sd (eSorts e)
  return (e {eSorts = s', eSpec = eSpec e Q.|> SSort v sd})

insertDecl :: Ident -> Decl -> Environment -> Either String Environment
insertDecl v d e = do
  trace ("insertDecl " ++ v ++ ": " ++ show d) (return ())
  d' <- insertNew ("decl " ++ v ++ " already declared") v d (eDecls e)
  return (e {eDecls = d', eSpec = eSpec e Q.|> SDecl v d})

insertSpec :: Spec -> Environment -> Either String Environment
insertSpec (SSort v sd) e = insertSort v sd e
insertSpec (SDecl v d) e = insertDecl v d e
insertSpec s e = return (e {eSpec = eSpec e Q.|> s})
