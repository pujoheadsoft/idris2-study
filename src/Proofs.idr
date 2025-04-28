module Proofs

{-
  [等価性]
  data Equal : forall a, b . a -> b -> Type where
    反射性(Reflexivity)
    xRx 値が等しいペアのとき、必ず関係が成立する(自分自身に対して必ず関係性を持つ)。
    反射性を満たす例の一つが = である。
    ↓のxは暗黙引数なので、推測できれば省略できる。
    Refl : {0 x : a} -> Equal x x

  [Equalの演算子]
  (~=~) : (x : a) -> (y : b) -> Type
  (~=~) = Equal

  [対称性]
  sym : (0 rule : x ~=~ y) -> y ~=~ x
  sym Refl = Refl

  [replace]
  x = y であることの証明 rule と x に関する性質 p が成り立つことの証明 p x が与えられたとき
  y に関して同じ性質 p が成り立つことの証明 p y を返す。
  x と y が同じならば、どちらも同じ性質が成り立つと言えるということか。
  replace : forall x, y, p . (0 rule : x = y) -> (1 _ : p x) -> p y
  replace Refl prf = prf

  [rewrite]
  rewriteはreplaceを自動化するようなやつ。
  replaceではpを推論するのが難しい場合があるので、pを明示的に指定できる。
  rewrite prf in expr という構文において、prf が x = y であることの証明であるならば、
  Idrisは expr の期待される型（現在の証明の穴 ? の型など）の中に現れる x を探し、それを y に置き換える。

  rewrite__impl : {0 x, y : a} -> (0 p : _) ->
                  (0 rule : x = y) -> (1 val : p y) -> p x
  rewrite__impl p Refl prf = prf
  %rewrite Equal rewrite__impl

  [trans]
  推移律: a = b, b = c ならば a = c であることの証明
  trans : forall a, b, c . (0 l : a = b) -> (0 r : b = c) -> a = c
  trans Refl Refl = Refl

  [cong]
  合同関係: a = b ならば f a = f b であることの証明
  cong : (0 f : t -> u) -> (0 p : a = b) -> f a = f b
  cong f Refl = Refl
-}

{- 対称性を自前で実装してみる -}
-- sym : (0 _ : x = y) -> y = x を使った版。symはそのまんま対称性なので、ほぼやる意味がない実装。
symmetry1 : a = b -> b = a
symmetry1 prf = sym prf

-- replace : (0 rule : x = y) -> p x -> p y を使った版
-- pを推論できなかったので明示している
symmetry2 : a = b -> b = a
symmetry2 prf = replace {p = \k => k = a} prf Refl

-- rewriteを使った版。replace版と異なりpを明示する必要がない。
symmetry3 : a = b -> b = a
symmetry3 prf = rewrite prf in Refl

{- 推移律を自前で実装してみる -}
-- transを使った版
trans1 : (a = b) -> (b = c) -> (a = c)
trans1 p1 p2 = trans p1 p2

-- replaceを使った版
trans2 : (a = b) -> (b = c) -> (a = c)
trans2 p1 p2 = rewrite p1 in p2

-- 自動で証明できる
p1_plus_1 : 1 + 1 = 2
p1_plus_1 = Refl { x = 1 + 1 }

-- 変数が絡むと自動で証明できなくなる
n_plus_1 : (n : Nat) -> n + 1 = 1 + n
n_plus_1 Z = Refl { x = 1 + Z }
n_plus_1 (S n) = rewrite (n_plus_1 n) in Refl { x = 1 + S n } -- 再帰的に証明

{-
  これも自動で証明できない
  では、なぜReflはある等式は証明できるが、他の等式は証明できないのだろうか？

  第一の答えは、この例のplusは第一引数の再帰によって定義されるからである。
  Reflだけで証明できる等式は「定義的等式」と呼ばれる。
  定義的に等しいためには、方程式の両辺が同じ値に正規化されなければならない。

  つまり、Idrisで1+1と入力すると、定義的等式が組み込まれているので、即座に2になる。
-}
plusReducesR : (n : Nat) -> plus n Z = n
plusReducesR Z = Refl
plusReducesR (S n) = rewrite (plusReducesR n) in Refl { x = Z + S n }

-- 一方、これは定数がplusの第一引数に来ているので、定義的等式が成り立つ。だからReflで証明できる。
plusReducesL : (n : Nat) -> plus Z n = n
plusReducesL n = Refl