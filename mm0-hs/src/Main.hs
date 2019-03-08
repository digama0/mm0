module Main (main) where
import System.Environment
import qualified Data.ByteString.Lazy as B
import Parser
import AST

main :: IO ()
main = do
  s <- B.getContents
  ast <- either fail pure (parse s)
  print ast
