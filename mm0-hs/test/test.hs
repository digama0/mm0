import Test.Tasty
import Test.Compiler

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [compilerTests]
