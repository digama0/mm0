module Main (main) where
import System.Environment
import qualified Data.ByteString.Lazy as B
import Parser
import AST
import Util
import Elaborate

liftIO :: Either String a -> IO a
liftIO (Left e) = fail e
liftIO (Right e) = return e

main :: IO ()
main = do
  s <- B.getContents
  ast <- either fail pure (parse s)
  -- print ast
  putStr "\n"
  pos <- liftIO (elabAST ast)
  print pos
