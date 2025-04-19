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

fin2_5 : Fin 5
fin2_5 = FS (FS FZ)

fin2_6 : Fin 6
fin2_6 = FS (FS FZ)

fin4_5 : Fin 5
fin4_5 = FS (FS (FS (FS FZ)))

fin4_6 : Fin 6
fin4_6 = FS (FS (FS (FS FZ)))

it : String -> IO() -> IO ()
it description test = do
  putStr $ description ++ ": "
  test

export
spec : IO ()
spec = do
  it "test replicate" $ do
    let vec = replicate 5 1
    assertEq vec [1, 1, 1, 1, 1]
  
  it "test replicate (下線文字を使う)" $ do
    let
      vec : Vect 3 Integer 
      vec = zipWith (*) (replicate _ 10) (replicate _ 11)
    assertEq vec [110, 110, 110]

  it "test replicate'" $ do
    let
      vec : Vect 3 Integer 
      vec = zipWith (*) (replicate' 10) (replicate' 11)
    assertEq vec [110, 110, 110]

  it "test head" $ do
    let vec = [4, 2, 3]
    let result = DependentType.head vec
    assertEq result 4

  it "test tail" $ do
    let vec = [4, 2, 3]
    let result = DependentType.tail vec
    assertEq result [2, 3]
  
  it "test zipWith3" $ do
    let vec1 = [1, 2, 3]
    let vec2 = [4, 5, 6]
    let vec3 = [7, 8, 9]
    let result = zipWith3 (\a, b, c => a + b + c) vec1 vec2 vec3
    assertEq result [12, 15, 18]
  
  it "test foldSemi" $ do
    let vec = ["x", "y", "z"]
    let result = foldSemi vec
    assertEq result (Just "xyz")
  
  it "test foldSemiVect" $ do
    let vec = ["x", "y", "z"]
    let result = foldSemiVect vec
    assertEq result "xyz"
  
  it "test iterate" $ do
    let vec = iterate 5 0 (+ 1)
    assertEq vec [0, 1, 2, 3, 4]
  
  it "test generate" $ do
    let vec = generate 5 (\s => (s + 1, s)) 0
    assertEq vec [0, 1, 2, 3, 4]
  
  it "test fromList" $ do
    let vec = fromList [1, 2, 3]
    assertEq vec [1, 2, 3]
  
  it "test maybeSize Just" $ do
    let vec = Just 1
    let result = maybeSize vec
    assertEq result 1
    
  it "test maybeSize Nothing" $ do
    let vec : Maybe Integer
        vec = Nothing
    let result = maybeSize vec
    assertEq result 0
  
  it "test fromMaybe" $ do
    let vec = Just 1
    let result = fromMaybe (Just "x")
    assertEq result ["x"]

  it "test fromMaybe (Nothing)" $ do
    let vec : Maybe Integer
        vec = Nothing
    let result = fromMaybe vec
    assertEq result []

  it "test index" $ do
    let vec = [1, 2, 3, 4, 5]
    let result = index fin4_5 vec
    assertEq result 5

  it "test update" $ do
    let vec = [1, 2, 3]
    let result = update (+1) fin1_3 vec
    assertEq result [1, 3, 3]

  it "test insert" $ do
    let vec = [1, 2, 3, 4]
    let result = insert fin4_5 5 vec
    assertEq result [1, 2, 3, 4, 5]

  it "test delete" $ do
    let vec = [1, 2, 3, 4, 5]
    let result = delete fin0_5 vec
    assertEq result [2, 3, 4, 5]
  
  it "safeIndexList" $ do
    let
      list : List Integer 
      list = [1, 2, 3]
    let result = safeIndexList list fin1_3
    assertEq result 2
  
  it "test finToNat" $ do
    let result = finToNat fin4_5
    assertEq result 4
  
  it "test take" $ do
    let vec = ["a", "b", "c", "d", "e"]
    let result = take fin4_6 vec
    assertEq result ["a", "b", "c", "d"]

  it "test take'" $ do
    let vec = ["a", "b", "c", "d", "e"]
    let result = take' 4 vec
    assertEq result ["a", "b", "c", "d"]

  it "test minus" $ do
    let result = minus 5 fin4_6
    assertEq result 1
  
  it "test drop" $ do
    let vec = [1, 2, 3, 4]
    let result = drop fin2_5 vec
    assertEq result [3, 4]

  it "test drop'" $ do
    let vec = [1, 2, 3, 4]
    let result = drop' 2 vec
    assertEq result [3, 4]

  it "test splitAt" $ do
    let vec = [1, 2, 3, 4, 5]
    let result = splitAt fin2_6 vec
    assertEq result ([1, 2], [3, 4, 5])

  it "test splitAt'" $ do
    let vec = [1, 2, 3, 4, 5]
    let result = splitAt' 2 vec
    assertEq result ([1, 2], [3, 4, 5])

  it "test Vect ++" $ do
    let vec1 = [1, 2, 3]
    let vec2 = [4, 5, 6]
    let result = DependentType.(++) vec1  vec2
    assertEq result [1, 2, 3, 4, 5, 6]
  
  it "test flattenList" $ do
    let list = [[1, 2], [3, 4], [5]]
    let result = flattenList list
    assertEq result [1, 2, 3, 4, 5]
  
  it "test flattenVect" $ do
    let vec = [[1, 2], [3, 4], [5, 6]]
    let result = flattenVect vec
    assertEq result [1, 2, 3, 4, 5, 6]