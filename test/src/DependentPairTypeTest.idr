module DependentPairTypeTest

import DependentPairType
import Data.Vect
import Data.DPair
import Data.Singleton
import Test

three : Singleton 3
three = Val 3

three' : Singleton 3
three' = Val 3

Eq (Singleton 3) where
  (Val 3) == (Val 3) = True
  _ == _ = False

-- こうすればshowができる。。。
Show (Singleton 3) where
  show (Val _) = show 3

public export
spec : IO ()
spec = do
  it "test takeWhile" $ do
    let
      vec : Vect 3 Integer
      vec = [1, 2, 3]
    let r = takeWhile' (\x => x < 3) vec
    case r of
      (2 ** r) => r `shouldBe` [1, 2]
      (l ** _) => failure ("expected Vect length 2, but " ++ show l)
  
  it "test takeWhileExists" $ do
    let
      vec : Vect 3 Integer
      vec = [1, 2, 3]
    let e = takeWhileExists (\x => x < 3) vec
    let r = toDPair e
    case r of
      (2 ** r) => r `shouldBe` [1, 2]
      (l ** _) => failure ("expected Vect length 2, but " ++ show l)
  
  it "test filterVect" $ do
    let
      vec : Vect 3 Integer
      vec = [1, 2, 3]
    let r = filterVect (\x => x < 3) vec
    case r of
      (2 ** r) => r `shouldBe` [1, 2]
      (l ** _) => failure ("expected Vect length 2, but " ++ show l)

  it "test mapMaybeVect" $ do
    let
      vec : Vect 3 Integer
      vec = [1, 2, 3]
    let r = mapMaybeVect (\x => if x < 3 then Just (x + 1) else Nothing) vec
    case r of
      (2 ** r) => r `shouldBe` [2, 3]
      (l ** _) => failure ("expected Vect length 2, but " ++ show l)
  
  it "test dropWhileVect" $ do
    let
      vec : Vect 3 Integer
      vec = [1, 2, 3]
    let e = dropWhileVect (\x => x < 3) vec
    let r = toDPair e
    case r of
      (1 ** r) => r `shouldBe` [3]
      (l ** _) => failure ("expected Vect length 1, but " ++ show l)