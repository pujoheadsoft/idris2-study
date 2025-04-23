module Predicates

import Decidable.Equality

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