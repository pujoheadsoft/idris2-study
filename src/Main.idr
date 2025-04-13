module Main

main : IO ()
main = putStrLn "Hello from Idris2!"

data Vect : (len : Nat) -> (a :Type) -> Type where
  Nil : Vect 0 a
  (::) : (x : a) -> (xs : Vect n a) -> Vect (S n) a

vec0 : Vect 0 Integer
vec0 = Nil

vec1 : Vect 1 Integer
vec1 = [12]

vec2 : Vect 2 Integer
vec2 = [12, 13] -- 12 :: vec1 でもいい

-- 暗黙引数を明示しているが、(a -> b) -> Vect n a -> Vect n b でいい
mapVect : {0 a, b : _} -> {0 n : Nat} -> (a -> b) -> Vect n a -> Vect n b
mapVect _ Nil = Nil
mapVect f (x :: xs) = f x :: mapVect f xs

zipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith f [] [] = Nil
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys
zipWith _ [] (_ :: _) impossible -- Idrisが自分で「不可能であること」を導出できるけど明示する場合impossibleが使える
zipWith _ (_ :: _) [] impossible

replicate : (n : Nat) -> a -> Vect n a
replicate 0 _ = Nil
replicate (S k) va = va :: replicate k va
