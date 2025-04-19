{-
  依存ペア型、または依存和型、Σ型(シグマ型)
-}
module DependentPairType

import Data.Vect
import Data.DPair
import Data.Singleton

{-
  依存対の例
  ベクタとベクタの長さに合致する値が対になったもの
-}
record AnyVect a where
  constructor MkAnyVect
  length : Nat -- ベクタの長さ
  vect : Vect length a -- ベクタの値

{-
  一般的な依存対型(Preludeにある型なので'をつけている)
  AnyVectよりも一般的な型
  依存対とは、何らかの型の値を、最初の値から計算された型の2つ目の値と対にしたもの。

  型`a`と、関数`p`がある。
  `p`は型`a`の値を受け取り、型を返す関数。
-}
record DPair' (a : Type) (p : a -> Type) where
  constructor MkDPair'
  fst : a
  snd : p fst

-- DPair'として表現したAnyVect a
AnyVect' : (a : Type) -> Type
AnyVect' a = DPair' Nat (\n => Vect n a)

{-
  既存のDpair型を表現する特別な構文を用いた場合
  (n : Nat ** Vect n a)はREPLで調べると
  DPair Nat (\n => Vect n Int)に脱糖される
-}
AnyVect'' : (a : Type) -> Type
AnyVect'' a = (n : Nat ** Vect n a)

-- 上記の`n`は型`Nat`でなければいけないことを推論できるので省略することができる(括弧内に式を置く必要はある)
AnyVect''' : (a : Type) -> Type
AnyVect''' a = (n ** Vect n a)

takeWhile : (a -> Bool) -> Vect m a -> (n ** Vect n a)
takeWhile f [] = (_ ** []) -- 依存対を作るにも**の構文は使える
takeWhile f (x :: xs) = case f x of
  True => do
    let (_ ** ys) = takeWhile f xs -- **はパターンマッチにも使える
    (_ ** x :: ys)
  False => (_ ** [])

-- 依存対の構文を使って依存3対を作れる(それ以上もできる)
AnyMatrix : (a : Type) -> Type
AnyMatrix a = (m ** n ** Vect m (Vect n a))

{-
  実行時に指標を持ち回る必要がない場合※、特別版の依存対`Exists`を使うことができる。
  ※例えばベクタへのパターン合致により長さの指標を知ることができる。
  takeWhileExistsは、その例。

  `Exists`は最初の引数が数量子ゼロの依存対である（以下は定義）。
  数量子がゼロということはすなわち変数は実行時に消去されるということ
  record Exists {0 type : Type} this where
    constructor Evidence -- コンストラクタ名はMkXXXじゃなくてEvidence
    0 fst : type
    snd : this fst -- thisはfstを受け取る型
  
  ExistsをDPairと比べてみよう。
  record DPair a (p : a -> Type) where
    constructor MkDPair
    fst : a
    snd : p fst
-}
takeWhileExists : (a -> Bool) -> Vect m a -> Exists (\n => Vect n a)
takeWhileExists f [] = Evidence _ []
takeWhileExists f (x :: xs) = case f x of
  True => let Evidence _ ys = takeWhileExists f xs
          in Evidence _ (x :: ys)
  False => takeWhileExists f xs

{-
  単独型(Singleton)の例
  Singletonは保有する値を引数にとる型
  固定値以外の値を返すことは型エラーとなる

  vectLengthは、ベクタの長さを返す関数
  Data.Vector.lengthより強い保証がついてくる。
  すぐ下にlength'としてData.Vector.lengthの実装を載せているが、これは更に下に定義した
  bogusLengthのようにインチキな実装をしてしまうことができる。
-}
vectLength : Vect n a -> Singleton n
vectLength [] = Val 0
vectLength (x :: xs) =
  let Val l = vectLength xs
  in Val (S l)

length' : (xs : Vect len elem) -> Nat
length' [] = 0
length' (_::xs) = 1 + length' xs

-- これはインチキな実装(型で保証できていない)
bogusLength : (xs : Vect len elem) -> Nat
bogusLength = const 0

