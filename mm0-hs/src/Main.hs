module Main (main) where

import System.IO
import System.Exit
import System.Environment
import System.Timeout
import qualified Data.ByteString.Lazy as B
import Parser
import AST
import Util
import Elaborator
import Verifier
import ProofTextParser
import FromMM
import ToHolIO

main :: IO ()
main = do
  getArgs >>= \case
    "verify" : rest -> doVerify rest
    "from-mm" : rest -> fromMM rest
    "show-bundled" : rest -> showBundled rest
    "to-hol" : rest -> toHolIO rest
    _ -> die ("incorrect args; use\n" ++
      "  mm0-hs verify MM0-FILE MMU-FILE\n" ++
      "  mm0-hs show-bundled MM-FILE\n" ++
      "  mm0-hs from-mm MM-FILE [-o MM0-FILE MMU-FILE]\n" ++
      "  mm0-hs to-hol MM0-FILE MMU-FILE\n")

doVerify :: [String] -> IO ()
doVerify args = do
  (mm0, rest) <- case args of
    [] -> return (stdin, [])
    (mm0:r) -> (\h -> (h, r)) <$> openFile mm0 ReadMode
  s <- B.hGetContents mm0
  ast <- either die pure (parse s)
  env <- liftIO (elabAST ast)
  putStrLn "spec checked"
  case rest of
    [] -> die "error: no proof file"
    (mmp:_) -> do
      pf <- B.readFile mmp
      pf <- liftIO (parseProof pf)
      out <- liftIO (verify s env pf)
      if null out then putStrLn "verified"
      else mapM_ putStr out
