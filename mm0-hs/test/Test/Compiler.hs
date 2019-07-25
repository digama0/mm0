module Test.Compiler where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Text as T
import MM0.Compiler.Env
import MM0.Compiler.AST
import MM0.Compiler.Parser

compilerTests :: TestTree
compilerTests = testGroup "Compiler" [alphanumberTests, parserTests]

alphanumberTests :: TestTree
alphanumberTests = testGroup "alphanumber" $
  map (\(a, b) -> testCase (show a ++ " -> " ++ T.unpack b) $ alphanumber a @?= b) $
    [(0, "a"), (1, "b"), (25, "z"), (26, "aa"), (26*2-1, "az"),
     (26*2, "ba"), (26*27-1, "zz"), (26*27, "aaa"), (26*27+1, "aab")]

parserTests :: TestTree
parserTests = testGroup "Parser" [
  testCase "parse (foo bar)" $ do
    runParser lispVal "" 0 "(foo bar)  " @?=
      ([], 11, Just $ Span (0, 9) $ AList [
        Span (1, 4) $ AAtom "foo",
        Span (5, 8) $ AAtom "bar"]) ]
