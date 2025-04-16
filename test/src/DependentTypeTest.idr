module DependentTypeTest

import DependentType

assertEq : (Show a, Eq a) => (given : a) -> (expected : a) -> IO ()
assertEq g e = if g == e 
  then putStrLn "✅ Test Passed"
  else putStrLn ("❌ Test Failed\n  expected: " ++ show e ++ "\n    actual: " ++ show g)

vec0 : Vect 0 Integer
vec0 = Nil

vec1 : Vect 1 Integer
vec1 = [12]

vec2 : Vect 2 Integer
vec2 = [12, 13] -- 12 :: vec1 でもいい

fin0_5 : Fin 5
fin0_5 = FZ

fin0_7 : Fin 7
fin0_7 = FZ

fin1_3 : Fin 3
fin1_3 = FS FZ

fin4_5 : Fin 5
fin4_5 = FS (FS (FS (FS FZ)))

it : String -> IO() -> IO ()
it description test = do
  putStr $ description ++ ": "
  test

export
spec : IO ()
spec = do
  it "test update" $ do
    let vec = [1, 2, 3]
    let result = update (+1) fin1_3 vec
    assertEq result [1, 3, 3]

  it "test delete" $ do
    let vec = [1, 2, 3, 4, 5]
    let result = delete fin0_5 vec
    assertEq result [2, 3, 4, 5]