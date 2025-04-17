module DependentType

public export
data Vect : (len : Nat) -> (a :Type) -> Type where
  Nil : Vect 0 a
  (::) : (x : a) -> (xs : Vect n a) -> Vect (S n) a

public export
Eq a => Eq (Vect n a) where
  Nil == Nil = True
  (x :: xs) == (y :: ys) = x == y && xs == ys

public export
Show a => Show (Vect n a) where
  show xs = "[" ++ showItems xs ++ "]"
    where
      showItems : Vect m a -> String
      showItems Nil = ""
      showItems (x :: Nil) = show x
      showItems (x :: xs) = show x ++ ", " ++ showItems xs

-- 暗黙引数を明示しているが、(a -> b) -> Vect n a -> Vect n b でいい
public export
mapVect : {0 a, b : _} -> {0 n : Nat} -> (a -> b) -> Vect n a -> Vect n b
mapVect _ Nil = Nil
mapVect f (x :: xs) = f x :: mapVect f xs

public export
zipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith f [] [] = Nil
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys
zipWith _ [] (_ :: _) impossible -- Idrisが自分で「不可能であること」を導出できるけど明示する場合impossibleが使える
zipWith _ (_ :: _) [] impossible

public export
replicate : (n : Nat) -> a -> Vect n a
replicate 0 _ = Nil
replicate (S k) va = va :: replicate k va

public export
-- 制約なし数量子の暗黙引数として n を渡す
replicate' : {n : _} -> a -> Vect n a
replicate' = replicate n

-- 演習1
public export
head : Vect (S n) a -> a
head (x :: xs) = x

-- 演習2
public export
tail : Vect (S n) a -> Vect n a
tail (x :: xs) = xs

-- 演習3
public export
zipWith3 : (a -> b -> c -> d) -> Vect n a -> Vect n b -> Vect n c -> Vect n d
zipWith3 f [] [] [] = Nil
zipWith3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: zipWith3 f xs ys zs

-- 演習4
public export
foldSemi : Semigroup a => List a -> Maybe a
foldSemi [] = Nothing
-- foldSemi (x :: xs) = do
--   let result = foldSemi xs
--   Just $ case result of
--     Nothing => x
--     Just y => (x <+> y)
foldSemi (x :: xs) = pure . (maybe x (x <+>)) $ foldSemi xs

-- 演習5
public export
foldSemiVect : Semigroup a => Vect (S n) a -> a
foldSemiVect (x :: []) = x
foldSemiVect (x :: t@(_ :: _)) = x <+> foldSemiVect t

-- 演習6
public export
iterate : (n : Nat) -> a -> (a -> a) -> Vect n a
iterate 0 _ _ = Nil
iterate (S n) a f = a :: iterate n (f a) f

-- 演習7
public export
generate : (n : Nat) -> (s -> (s, a)) -> s -> Vect n a
generate 0 _ _ = Nil
generate (S n) f s = do
  let (s', a) = f s
  a :: generate n f s'

-- 演習8
public export
fromList : (as : List a) -> Vect (length as) a
fromList [] = Nil
fromList (x :: xs) = x :: fromList xs

-- 演習9
public export
maybeSize : Maybe a -> Nat
maybeSize Nothing = 0
maybeSize (Just _) = 1

public export
fromMaybe : (m : Maybe a) -> Vect (maybeSize m) a
fromMaybe Nothing = Nil
fromMaybe (Just x) = [x]

-- 有限集合の要素を表す型
public export
data Fin : (n : Nat) -> Type where
  FZ : {0 n : Nat} -> Fin (S n) -- 0を表す
  FS : (k : Fin n) -> Fin (S n) -- k+1を表す(後続の数)

public export
index : Fin n -> Vect n a -> a
index FZ (x :: _) = x
index (FS k) (_ :: xs) = index k xs

-- 演習その2-1
public export
update : (a -> a) -> Fin n -> Vect n a -> Vect n a
update f FZ (x :: xs) = f x :: xs
update f (FS k) (x :: xs) = x :: update f k xs

-- 演習その2-2
public export
insert : Fin (S n) -> a -> Vect n a -> Vect (S n) a
insert FZ a x = a :: x
insert (FS k) a (x :: xs) = x :: insert k a xs

-- 演習その2-3
public export
delete : Fin (S n) -> Vect (S n) a -> Vect n a
delete FZ (_ :: xs) = xs
delete (FS k) (x :: xs@(_ :: _)) = x :: delete k xs -- xs@(_ :: _)で少なくとも1要素あることを保証している

-- 演習その2-4
public export
safeIndexList : (xs : List a) -> Fin (length xs) -> a
safeIndexList [] _ impossible
safeIndexList (x :: _) FZ = x
safeIndexList (_ :: xs) (FS k) = safeIndexList xs k

-- 演習その2-5
public export
finToNat : Fin n -> Nat
finToNat FZ = 0
finToNat (FS k) = 1 + finToNat k

-- 演習その2-5-2
public export
take : (k : Fin (S n)) -> Vect n a -> Vect (finToNat k) a
take FZ _ = []
take (FS k) (x :: xs) = x :: take k xs

-- 演習その2-5-3
public export
minus : (n : Nat) -> Fin (S n) -> Nat
minus n FZ = n
minus (S n) (FS k) = minus n k

public export
(++) : Vect m a -> Vect n a -> Vect (m + n) a
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

public export
drop' : (m : Nat) -> Vect (m + n) a -> Vect n a
drop' 0 xs = xs
drop' (S n) (_ :: xs) = drop' n xs

public export
flattenList : List (List a) -> List a
flattenList [] = []
flattenList (xs :: xss) = xs ++ flattenList xss

-- 演習3-1
public export
flattenVect : Vect n (Vect m a) -> Vect (n * m) a
flattenVect [] = []
flattenVect (xs :: xss) = (++) xs (flattenVect xss)

-- 演習3-2
public export
take' : (m : Nat) -> Vect (m + n) a -> Vect m a
take' 0 xs = []
take' (S n) (x :: xs) = x :: take' n xs