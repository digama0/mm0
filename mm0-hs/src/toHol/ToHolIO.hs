module ToHolIO where

import Control.Monad
import System.IO
import System.Exit
import Data.List
import qualified Data.ByteString.Lazy as B
import Parser
import AST
import Elaborator
import Verifier
import ProofTextParser
import ToHol
import HolCheck
import ToOpenTheory
import ToLean
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
  pf <- B.readFile mmp
  pf <- liftIO (parseProof pf)
  hol <- liftIO (toHol env pf)
  write $ \h -> do
    hSetNewlineMode h (NewlineMode LF LF)
    writeOT (hPutStrLn h) hol
toOpenTheory _ = die "to-othy: incorrect args; use 'to-othy MM0-FILE MMU-FILE [-o out.art]'"

toLean :: [String] -> IO ()
toLean (mm0 : mmp : rest) = do
  (nax, rest) <- return $ case rest of
    "-a" : pre : rest -> (FromFile pre, rest)
    "+a" : rest -> (Only, rest)
    rest -> (Regular, rest)
  (cs, rest) <- return $ case rest of
    "-c" : n : rest -> (read n, rest)
    rest -> (maxBound, rest)
  bn <- case rest of
    "-o" : file : _ -> return file
    _ -> die "to-lean: -o FILE.LEAN required"
  mm0 <- openFile mm0 ReadMode
  s <- B.hGetContents mm0
  ast <- either die pure (parse s)
  env <- liftIO (elabAST ast)
  pf <- B.readFile mmp
  pf <- liftIO (parseProof pf)
  hol <- liftIO (toHol env pf)
  writeLean nax bn cs hol
toLean _ = die "to-lean: incorrect args; use 'to-lean MM0-FILE MMU-FILE [-o out.lean]'"
