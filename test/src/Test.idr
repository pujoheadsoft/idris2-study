module Test

public export
assertEq : (Show a, Eq a) => (given : a) -> (expected : a) -> IO ()
assertEq g e = if g == e 
  then putStrLn "✅ Test Passed"
  else putStrLn ("❌ Test Failed\n  expected: " ++ show e ++ "\n    actual: " ++ show g)

public export
it : String -> IO() -> IO ()
it description test = do
  putStr $ description ++ ": "
  test