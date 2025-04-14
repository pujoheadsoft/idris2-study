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

-- 演習1
head : Vect (S n) a -> a
head (x :: xs) = x

-- 演習2
tail : Vect (S n) a -> Vect n a
tail (x :: xs) = xs

-- 演習3
zipWith3 : (a -> b -> c -> d) -> Vect n a -> Vect n b -> Vect n c -> Vect n d
zipWith3 f [] [] [] = Nil
zipWith3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: zipWith3 f xs ys zs

-- 演習4
foldSemi : Semigroup a => List a -> Maybe a
foldSemi [] = Nothing
foldSemi (x :: xs) = Just x <+> foldSemi xs

-- 演習5
foldSemiVect : Semigroup a => Vect (S n) a -> a
foldSemiVect (x :: []) = x
foldSemiVect (x :: t@(_ :: _)) = x <+> foldSemiVect t