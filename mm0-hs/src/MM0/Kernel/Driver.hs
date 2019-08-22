module MM0.Kernel.Driver where

import Control.Monad
import System.IO
import System.Exit
import qualified Data.ByteString.Lazy as B
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
    (mm0:r) -> (\h -> (h, r)) <$> openFile mm0 ReadMode
  s <- B.hGetContents mm0
  ast <- either (die . show) pure (parse s)
  env <- liftIO' $ elabAST ast
  putStrLn "spec checked"
  case rest of
    [] -> die "error: no proof file"
    mmp : rest' -> do
      pff <- B.readFile mmp
      pf <- liftIO' $ parseProof pff
      out <- liftIO' $ verify s env pf
      when (not (null out)) $ mapM_ B.putStr out >> exitFailure
      putStrLn "verified"
      case rest' of
        "-S" : "-o" : mmb : _ -> exportK True mmb env pf
        "-o" : mmb : _ -> exportK False mmb env pf
        _ -> return ()
