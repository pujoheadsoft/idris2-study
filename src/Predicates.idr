module Predicates

import Decidable.Equality
import Data.HList

%default total

-- List a でも十分だが、慣習的に名付けるっぽい
data NonEmpty : (as : List a) -> Type where
  IsNonEmpty : NonEmpty (x :: xs)

head1 : (as : List a) -> (0 _ : NonEmpty as) -> a
head1 (h :: _) _ = h
head1 [] IsNonEmpty impossible

headEx1 : Nat
headEx1 = head1 [1, 2, 3] IsNonEmpty

{-
  Uninhabitedはインタフェース

  ある型が空であることの正準証明。
  tがあれば矛盾があった。
  Uninhabited : Type -> Type
    uninhabited : t -> Void
-}
Uninhabited (NonEmpty []) where
  uninhabited IsNonEmpty impossible

nonEmpty : (as : List a) -> Dec (NonEmpty as)
nonEmpty (x :: xs) = Yes IsNonEmpty
nonEmpty [] = No uninhabited
{-
DecはDecidability(決定可能性)を表す。
data Dec : Type -> Type where
  ||| @ prf は証明
  Yes : (prf : prop) -> Dec prop

  ||| propを保持することが矛盾する場合
  No  : (contra : Not prop) -> Dec prop

export Uninhabited (Yes p === No q) where uninhabited eq impossible
export Uninhabited (No p === Yes q) where uninhabited eq impossible
-}

headMaybe1 : List a -> Maybe a
headMaybe1 as = case nonEmpty as of
  Yes prf => Just $ head1 as prf
  No _ => Nothing

{-
  暗黙引数prfの数量子0の前のautoは、この値をIdrisに自力で構築してもらいたいということ。
  autoは自動暗黙子で、こういう引数は自動暗黙引数という。
-}
head : (as : List a) -> {auto 0 prf : NonEmpty as} -> a
head (x :: _) = x
head [] impossible

-- {auto 0 prf : NonEmpty as} -> a は (0 _ : NonEmpty as) => a と書ける
head' : (as : List a) -> (0 _ : NonEmpty as) => a
head' (x :: _) = x
head' [] impossible

-- 制約の名前が不要なら t => a のように書ける。
head'' : (as : List a) -> NonEmpty as => a
head'' (x :: _) = x
head'' [] impossible

-- 使用例
headEx2 : Nat
headEx2 = Predicates.head [1, 2, 3]

headEx3 : Nat
headEx3 = Predicates.head' [1, 2, 3]

headEx4 : Nat
headEx4 = Predicates.head'' [1, 2, 3]

-- エラーになる例
-- Can't find an implementation for NonEmpty [].
-- errorHead : Nat
-- errorHead = Predicates.head []

headMaybe : List a -> Maybe a
headMaybe as = case nonEmpty as of
  Yes _ => Just $ Predicates.head as
  No _ => Nothing

-- 演習 1-1
tail : (as : List a) -> (0 _ : NonEmpty as) => List a
tail (_ :: xs) = xs

-- 演習 1-2
concat1 : Semigroup a => (as : List a) -> (0 _ : NonEmpty as) => a
concat1 (x :: xs) = foldl (<+>) x xs

-- 演習 1-3
max : Ord a => (as : List a) -> (0 _ : NonEmpty as) => a
max (x :: xs) = foldl Prelude.max x xs

min : Ord a => (as : List a) -> (0 _ : NonEmpty as) => a
min (x :: xs) = foldl Prelude.min x xs

-- 演習 1-4
-- 厳密な正の自然数のための述語
data StrictNatualNum : Nat -> Type where
  IsStrictNaturalNum : StrictNatualNum (S n)

safeDiv : (x : Nat) -> (y : Nat) -> (0 _ : StrictNatualNum y) => Nat
safeDiv x (S y) = go 0 x y
  where
    -- res: 累積結果, rem: 余り, sub: 減算回数
    go : (res, rem, sub : Nat) -> Nat
    go res 0 _ = res                      -- 余りが0なら結果を返す
    go res (S rem) 0 = go (res + 1) rem y -- 減算回数が0なら結果を+1して余りをリセット
    go res (S rem) (S sub) = go res rem sub   -- 減算回数があるなら、余りと減算回数を-1して再帰

safeDivEx1 : Nat
safeDivEx1 = 10 `safeDiv` 3

-- 演習 1-5
data IsJust : Maybe a -> Type where
  ItIsJust : IsJust (Just v)

Uninhabited (IsJust Nothing) where
  uninhabited ItIsJust impossible

-- 決定可能であることを示す
isJust : (m : Maybe a) -> Dec (IsJust m)
isJust Nothing = No uninhabited
isJust (Just v) = Yes ItIsJust

fromJust : (m : Maybe a) -> (0 _ : IsJust m) => a
fromJust (Just v) = v
fromJust Nothing impossible

-- 演習 1-6
data IsLeft : Either l r -> Type where
  ItIsLeft : IsLeft (Left v)

Uninhabited (IsLeft (Right r)) where
  uninhabited ItIsLeft impossible

isLeft : (e : Either l r) -> Dec (IsLeft e)
isLeft (Left v) = Yes ItIsLeft
isLeft (Right r) = No uninhabited

fromLeft : (e : Either l r) -> (0 _ : IsLeft e) => l
fromLeft (Left v) = v
fromLeft (Right r) impossible

data IsRight : Either l r -> Type where
  ItIsRight : IsRight (Right v)

Uninhabited (IsRight (Left l)) where
  uninhabited ItIsRight impossible

isRight : (e : Either l r) -> Dec (IsRight e)
isRight (Left l) = No uninhabited
isRight (Right v) = Yes ItIsRight

fromRight : (e : Either l r) -> (0 _ : IsRight e) => r
fromRight (Left l) impossible
fromRight (Right v) = v

-- ----------

data Elem : (elem : a) -> (as : List a) -> Type where
  Here : Elem x (x :: xs)
  There : Elem x xs -> Elem x (y :: xs)

-- 例
MyList : List Nat
MyList = [1, 3, 7]

elem1 : Elem 1 MyList
elem1 = Here

elem7 : Elem 7 MyList
elem7 = There (There Here)

get : (0 t : Type) -> HList ts -> (prf : Elem t ts) => t
get t (v :: vs) { prf = Here } = v
get t (v :: vs) { prf = There p } = get t vs { prf = p }
get _ [] impossible


getEx1 : Integer
getEx1 = get Integer ["foo", 1, False]

getEx2 : Maybe String
getEx2 = get (Maybe String) ["foo", Just "hello", False]