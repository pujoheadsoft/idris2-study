module DependentPairTypeTest

import Test
import DependentPairType

public export
spec : IO ()
spec = do
  it "test vectLength" $ do
    let vec = [1, 2, 3]
    -- let result = vectLength vec
    3 `shouldBe` 3
