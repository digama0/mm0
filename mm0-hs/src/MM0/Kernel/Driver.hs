module MM0.Kernel.Driver where

import Control.Monad
import System.IO
import System.Exit
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import MM0.FrontEnd.Parser
import MM0.Util
import MM0.FrontEnd.Elaborator
import MM0.Kernel.Verifier
import MM0.FrontEnd.ProofTextParser
import MM0.Compiler.Export

verifyIO :: [String] -> IO ()
verifyIO args = do
  (mm0, rest) <- case args of
    [] -> return (stdin, [])
    (mm0:r) -> (, r) <$> openFile mm0 ReadMode
  s <- BL.hGetContents mm0
  ast <- either (die . show) pure (parse s)
  env <- liftIO' $ elabAST ast
  putStrLn "spec checked"
  case rest of
    [] -> die "error: no proof file"
    mmp : _ -> do
      pf <- parseProofOrDie <$> B.readFile mmp
      out <- liftIO' $ verify s env pf
      when (not (null out)) $ mapM_ BL.putStr out >> exitFailure
      putStrLn "verified"

exportIO :: [String] -> IO ()
exportIO [] = die "error: no proof file"
exportIO (mmp : rest) = do
  pff <- B.readFile mmp
  let ppf = parseProof pff die
  case rest of
    "-S" : "-o" : mmb : _ -> exportKP True mmb ppf
    "-o" : mmb : _ -> exportKP False mmb ppf
    _ -> return ()
