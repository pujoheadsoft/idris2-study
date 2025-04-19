module DependentPairTypeTest

import Test
import DependentPairType

export
spec : IO ()
spec = do
  it "test vectLength" $ do
    let vec = [1, 2, 3]
    let result = vectLength vec
    result `shouldBe` 3
