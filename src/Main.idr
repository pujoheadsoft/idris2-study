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

-- 演習6
iterate : (n : Nat) -> a -> (a -> a) -> Vect n a
iterate 0 _ _ = Nil
iterate (S n) a f = a :: iterate n (f a) f

-- 演習7
generate : (n : Nat) -> (s -> (s, a)) -> s -> Vect n a
generate 0 _ _ = Nil
generate (S n) f s = do
  let (s', a) = f s
  a :: generate n f s'

-- 演習8
fromList : (as : List a) -> Vect (length as) a
fromList [] = Nil
fromList (x :: xs) = x :: fromList xs

-- 演習9
maybeSize : Maybe a -> Nat
maybeSize Nothing = 0
maybeSize (Just _) = 1

fromMaybe : (m : Maybe a) -> Vect (maybeSize m) a
fromMaybe Nothing = Nil
fromMaybe (Just x) = [x]

-- 有限集合の要素を表す型
data Fin : (n : Nat) -> Type where
  FZ : {0 n : Nat} -> Fin (S n) -- 0を表す
  FS : (k : Fin n) -> Fin (S n) -- k+1を表す(後続の数)

index : Fin n -> Vect n a -> a
index FZ (x :: _) = x
index (FS k) (_ :: xs) = index k xs

-- 演習その2-1
update : (a -> a) -> Fin n -> Vect n a -> Vect n a
update f FZ (x :: xs) = f x :: xs
update f (FS k) (x :: xs) = x :: update f k xs

-- 演習その2-2
insert : Fin (S n) -> a -> Vect n a -> Vect (S n) a
insert FZ a x = a :: x
insert (FS k) a (x :: xs) = x :: insert k a xs
