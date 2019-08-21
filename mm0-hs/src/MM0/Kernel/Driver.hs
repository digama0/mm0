module MM0.Kernel.Driver where

import System.IO
import System.Exit
import qualified Data.ByteString.Lazy as B
import MM0.FrontEnd.Parser
import MM0.Util
import MM0.FrontEnd.Elaborator
import MM0.Kernel.Verifier
import MM0.FrontEnd.ProofTextParser

verifyIO :: [String] -> IO ()
verifyIO args = do
  (mm0, rest) <- case args of
    [] -> return (stdin, [])
    (mm0:r) -> (\h -> (h, r)) <$> openFile mm0 ReadMode
  s <- B.hGetContents mm0
  ast <- either (die . show) pure (parse s)
  env <- liftIO' $ elabAST ast
  putStrLn "spec checked"
  case rest of
    [] -> die "error: no proof file"
    (mmp:_) -> do
      pff <- B.readFile mmp
      pf <- liftIO' $ parseProof pff
      out <- liftIO' $ verify s env pf
      if null out then putStrLn "verified"
      else mapM_ B.putStr out
