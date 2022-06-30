module MM0.HOL.ToHolIO where

import System.IO
import System.Exit
import qualified Data.ByteString as B
import MM0.FrontEnd.ProofTextParser
import MM0.HOL.ToHol
import MM0.HOL.Check
import MM0.HOL.ToOpenTheory
import MM0.HOL.ToLean
import MM0.HOL.ToLisp
import MM0.Util

toHolIO :: [String] -> IO ()
toHolIO (mmp : rest) = do
  let write = case rest of
        "-o" : hol : _ -> withFile hol WriteMode
        _ -> \k -> k stdout
  pf <- parseProofOrDie <$> B.readFile mmp
  hol <- liftIO' $ toHol pf
  write $ \h -> mapM_ (hPutStrLn h . flip shows "\n") hol
  _ <- liftIO' $ checkDecls hol
  putStrLn "verified HOL"
toHolIO _ = die "to-hol: incorrect args; use 'to-hol MMU-FILE [-o out.hol]'"

toOpenTheory :: [String] -> IO ()
toOpenTheory (mmp : rest) = do
  let write = case rest of
        "-o" : hol : _ -> withFile hol WriteMode
        _ -> \k -> k stdout
  pf <- parseProofOrDie <$> B.readFile mmp
  hol <- liftIO' $ toHol pf
  write $ \h -> do
    hSetNewlineMode h (NewlineMode LF LF)
    writeOT (hPutStrLn h) hol
toOpenTheory _ = die "to-othy: incorrect args; use 'to-othy MMU-FILE [-o out.art]'"

toLean :: [String] -> IO ()
toLean (mmp : rest) = do
  (nax, rest2) <- return $ case rest of
    "-a" : pre : rest2 -> (FromFile pre, rest2)
    "+a" : rest2 -> (Only, rest2)
    _ -> (Regular, rest)
  (cs, rest3) <- return $ case rest2 of
    "-c" : n : rest3 -> (read n, rest3)
    _ -> (maxBound, rest2)
  bn <- case rest3 of
    "-o" : file : _ -> return file
    _ -> die "to-lean: -o FILE.LEAN required"
  pf <- parseProofOrDie <$> B.readFile mmp
  hol <- liftIO' $ toHol pf
  writeLean nax bn cs hol
toLean _ = die "to-lean: incorrect args; use 'to-lean MMU-FILE [-o out.lean]'"

toLispIO :: [String] -> IO ()
toLispIO (mmp : rest) = do
  let write = case rest of
        "-o" : hol : _ -> withFile hol WriteMode
        _ -> \k -> k stdout
  pf <- parseProofOrDie <$> B.readFile mmp
  hol <- liftIO' $ toHol pf
  write $ \h -> mapM_ (hPutStrLn h . flip toLisp "\n") hol
toLispIO _ = die "to-lisp: incorrect args; use 'to-lisp MMU-FILE [-o out.lisp]'"
