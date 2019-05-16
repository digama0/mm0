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
import ToOpenTheory
import Util

toHolIO :: [String] -> IO ()
toHolIO (mm0 : mmp : rest) = do
  let write = case rest of
        "-o" : hol : _ -> withFile hol WriteMode
        _ -> \k -> k stdout
  mm0 <- openFile mm0 ReadMode
  s <- B.hGetContents mm0
  ast <- either die pure (parse s)
  env <- liftIO (elabAST ast)
  putStrLn "spec checked"
  pf <- B.readFile mmp
  pf <- liftIO (parseProof pf)
  hol <- liftIO (toHol env pf)
  write $ \h -> mapM_ (hPutStrLn h . flip shows "\n") hol
  liftIO $ checkDecls hol
  putStrLn "verified HOL"
toHolIO _ = die "to-hol: incorrect args; use 'to-hol MM0-FILE MMU-FILE [-o out.hol]'"

toOpenTheory :: [String] -> IO ()
toOpenTheory (mm0 : mmp : rest) = do
  let write = case rest of
        "-o" : hol : _ -> withFile hol WriteMode
        _ -> \k -> k stdout
  mm0 <- openFile mm0 ReadMode
  s <- B.hGetContents mm0
  ast <- either die pure (parse s)
  env <- liftIO (elabAST ast)
  putStrLn "spec checked"
  pf <- B.readFile mmp
  pf <- liftIO (parseProof pf)
  hol <- liftIO (toHol env pf)
  let ot = otToString hol
  write $ \h -> mapM_ (hPutStrLn h) ot
toOpenTheory _ = die "to-othy: incorrect args; use 'to-othy MM0-FILE MMU-FILE [-o out.art]'"
