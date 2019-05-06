module ToHolIO where

import Control.Monad
import System.IO
import System.Exit
import qualified Data.ByteString.Lazy as B
import Parser
import AST
import Elaborator
import Verifier
import ProofTextParser
import ToHol
import HolCheck
import Util

toHolIO :: [String] -> IO ()
toHolIO (mm0:mmp:_) = do
  mm0 <- openFile mm0 ReadMode
  s <- B.hGetContents mm0
  ast <- either die pure (parse s)
  env <- liftIO (elabAST ast)
  putStrLn "spec checked"
  pf <- B.readFile mmp
  pf <- liftIO (parseProof pf)
  hol <- liftIO (toHol env pf)
  mapM_ (putStrLn . flip shows "\n") hol
  liftIO $ fromJustError "HOL typecheck failed" (checkDecls hol >> return ())
  putStrLn "verified HOL"
toHolIO _ = die "to-hol: incorrect args; use 'to-hol MM0-FILE MMU-FILE'"
