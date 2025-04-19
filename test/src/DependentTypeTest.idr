module DependentTypeTest

import DependentType
import Test

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

export
spec : IO ()
spec = do
  it "test replicate" $ do
    let vec = replicate 5 1
    vec `shouldBe` [1, 1, 1, 1, 1]
  
  it "test replicate (下線文字を使う)" $ do
    let
      vec : Vect 3 Integer 
      vec = zipWith (*) (replicate _ 10) (replicate _ 11)
    vec `shouldBe` [110, 110, 110]

  it "test replicate'" $ do
    let
      vec : Vect 3 Integer 
      vec = zipWith (*) (replicate' 10) (replicate' 11)
    vec `shouldBe` [110, 110, 110]

  it "test head" $ do
    let vec = [4, 2, 3]
    let result = DependentType.head vec
    result `shouldBe` 4

  it "test tail" $ do
    let vec = [4, 2, 3]
    let result = DependentType.tail vec
    result `shouldBe` [2, 3]
  
  it "test zipWith3" $ do
    let vec1 = [1, 2, 3]
    let vec2 = [4, 5, 6]
    let vec3 = [7, 8, 9]
    let result = zipWith3 (\a, b, c => a + b + c) vec1 vec2 vec3
    result `shouldBe` [12, 15, 18]
  
  it "test foldSemi" $ do
    let vec = ["x", "y", "z"]
    let result = foldSemi vec
    result `shouldBe` (Just "xyz")
  
  it "test foldSemiVect" $ do
    let vec = ["x", "y", "z"]
    let result = foldSemiVect vec
    result `shouldBe` "xyz"
  
  it "test iterate" $ do
    let vec = iterate 5 0 (+ 1)
    vec `shouldBe` [0, 1, 2, 3, 4]
  
  it "test generate" $ do
    let vec = generate 5 (\s => (s + 1, s)) 0
    vec `shouldBe` [0, 1, 2, 3, 4]
  
  it "test fromList" $ do
    let vec = fromList [1, 2, 3]
    vec `shouldBe` [1, 2, 3]
  
  it "test maybeSize Just" $ do
    let vec = Just 1
    let result = maybeSize vec
    result `shouldBe` 1
    
  it "test maybeSize Nothing" $ do
    let vec : Maybe Integer
        vec = Nothing
    let result = maybeSize vec
    result `shouldBe` 0
  
  it "test fromMaybe" $ do
    let vec = Just 1
    let result = fromMaybe (Just "x")
    result `shouldBe` ["x"]

  it "test fromMaybe (Nothing)" $ do
    let vec : Maybe Integer
        vec = Nothing
    let result = fromMaybe vec
    result `shouldBe` []

  it "test index" $ do
    let vec = [1, 2, 3, 4, 5]
    let result = index fin4_5 vec
    result `shouldBe` 5

  it "test update" $ do
    let vec = [1, 2, 3]
    let result = update (+1) fin1_3 vec
    result `shouldBe` [1, 3, 3]

  it "test insert" $ do
    let vec = [1, 2, 3, 4]
    let result = insert fin4_5 5 vec
    result `shouldBe` [1, 2, 3, 4, 5]

  it "test delete" $ do
    let vec = [1, 2, 3, 4, 5]
    let result = delete fin0_5 vec
    result `shouldBe` [2, 3, 4, 5]
  
  it "safeIndexList" $ do
    let
      list : List Integer 
      list = [1, 2, 3]
    let result = safeIndexList list fin1_3
    result `shouldBe` 2
  
  it "test finToNat" $ do
    let result = finToNat fin4_5
    result `shouldBe` 4
  
  it "test take" $ do
    let vec = ["a", "b", "c", "d", "e"]
    let result = take fin4_6 vec
    result `shouldBe` ["a", "b", "c", "d"]

  it "test take'" $ do
    let vec = ["a", "b", "c", "d", "e"]
    let result = take' 4 vec
    result `shouldBe` ["a", "b", "c", "d"]

  it "test minus" $ do
    let result = minus 5 fin4_6
    result `shouldBe` 1
  
  it "test drop" $ do
    let vec = [1, 2, 3, 4]
    let result = drop fin2_5 vec
    result `shouldBe` [3, 4]

  it "test drop'" $ do
    let vec = [1, 2, 3, 4]
    let result = drop' 2 vec
    result `shouldBe` [3, 4]

  it "test splitAt" $ do
    let vec = [1, 2, 3, 4, 5]
    let result = splitAt fin2_6 vec
    result `shouldBe` ([1, 2], [3, 4, 5])

  it "test splitAt'" $ do
    let vec = [1, 2, 3, 4, 5]
    let result = splitAt' 2 vec
    result `shouldBe` ([1, 2], [3, 4, 5])

  it "test Vect ++" $ do
    let vec1 = [1, 2, 3]
    let vec2 = [4, 5, 6]
    let result = DependentType.(++) vec1  vec2
    result `shouldBe` [1, 2, 3, 4, 5, 6]
  
  it "test flattenList" $ do
    let list = [[1, 2], [3, 4], [5]]
    let result = flattenList list
    result `shouldBe` [1, 2, 3, 4, 5]
  
  it "test flattenVect" $ do
    let vec = [[1, 2], [3, 4], [5, 6]]
    let result = flattenVect vec
    result `shouldBe` [1, 2, 3, 4, 5, 6]
  
  it "test transpose" $ do
    let vec = [[1, 2, 3], [4, 5, 6]]
    let result = transpose vec
    result `shouldBe` [[1, 4], [2, 5], [3, 6]]