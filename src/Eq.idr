module Eq

import Data.Either
import Data.HList
import Data.Vect
import Data.String

%default total


public export
data ColType = I64 | Str | Boolean | Float

Eq ColType where
  I64     == I64     = True
  Str     == Str     = True
  Boolean == Boolean = True
  Float   == Float   = True
  _       == _       = False

public export
Schema : Type
Schema = List ColType

public export
IdrisType : ColType -> Type
IdrisType I64 = Int64
IdrisType Str = String
IdrisType Boolean = Bool
IdrisType Float = Double

public export
Row : Schema -> Type
Row = HList . map IdrisType

public export
record Table where
  constructor MkTable
  schema : Schema
  size : Nat
  rows : Vect size (Row schema)

data SameSchema : (s1 : Schema) -> (s2 : Schema) -> Type where
  Same : SameSchema s s

data SameColType : (c1, c2 : ColType) -> Type where
  SameCT : SameColType c c

sameColType : (c1, c2 : ColType) -> Maybe (SameColType c1 c2)
sameColType I64 I64 = Just SameCT
sameColType Str Str = Just SameCT
sameColType Boolean Boolean = Just SameCT
sameColType Float Float = Just SameCT
sameColType _ _ = Nothing


sameNil : SameSchema [] []
sameNil = Same

sameCons : SameColType c1 c2 -> SameSchema s1 s2 -> SameSchema (c1 :: s1) (c2 :: s2)
sameCons SameCT Same = Same

sameSchema : (s1, s2 : Schema) -> Maybe (SameSchema s1 s2)
sameSchema [] [] = Just sameNil
sameSchema [] (x :: xs) = Nothing
sameSchema (x :: xs) [] = Nothing
sameSchema (x :: xs) (y :: ys) = [| sameCons (sameColType x y) (sameSchema xs ys) |]

concatTables1 : Table -> Table -> Maybe Table
concatTables1 (MkTable schema1 size1 rows1) (MkTable schema2 size2 rows2) =
  case sameSchema schema1 schema2 of
    Just Same => Just $ MkTable schema1 _ (rows1 ++ rows2)
    Nothing => Nothing

{-
  命題の等値性を表す組み込み演算子===を使った版(=でもいいが紛らわしい)
  等値性を表す汎用的なデータ型は`Equal`で、c1 === c2は、Equal c1 c2と書ける。
  Equalの唯一のデータ型は`Refl`で、c1 === c2のときにだけ使える。
  すなわち eqColType I64 Str = Just Refl はコンパイルエラーになる。
-}
eqColType : (c1, c2 : ColType) -> Maybe (c1 === c2)
eqColType I64 I64 = Just Refl
eqColType Str Str = Just Refl
eqColType Boolean Boolean = Just Refl
eqColType Float Float = Just Refl
eqColType _ _ = Nothing

eqCons : {0 c1, c2 : a} -> {0 s1, s2 : List a} -> c1 === c2 -> s1 === s2 -> (c1 :: s1) === (c2 :: s2)
eqCons Refl Refl = Refl

eqSchema : (s1, s2 : Schema) -> Maybe (s1 === s2)
eqSchema [] [] = Just Refl
eqSchema [] (x :: xs) = Nothing
eqSchema (x :: xs) [] = Nothing
eqSchema (x :: xs) (y :: ys) = [| eqCons (eqColType x y) (eqSchema xs ys) |]

concatTables2 : Table -> Table -> Maybe Table
concatTables2 (MkTable schema1 size1 rows1) (MkTable schema2 size2 rows2) =
  case eqSchema schema1 schema2 of
    Just Refl => Just $ MkTable _ _ (rows1 ++ rows2)
    Nothing => Nothing

-- 演習1: SameColTypeが反射関係の一つであることを示す
sameColTypeReflexive : SameColType c c
sameColTypeReflexive = SameCT

-- 演習2: SameColTypeが対称関係の一つであることを示す
sameColTypeSymmetric : SameColType c1 c2 -> SameColType c2 c1
sameColTypeSymmetric SameCT = SameCT

-- 演習3: SameColTypeが推移関係の一つであることを示す
sameColTypeTransitive : SameColType c1 c2 -> SameColType c2 c3 -> SameColType c1 c3
sameColTypeTransitive SameCT SameCT = SameCT

-- 演習4
sameColTypeCong : (f: ColType -> a) -> SameColType c1 c2 -> f c1 === f c2
sameColTypeCong f SameCT = Refl

-- 演習5
-- cong : (0 f : (t -> u)) -> (0 _ : a = b) -> f a = f b は↑の一般化
natEq : (n1, n2 : Nat) -> Maybe (n1 === n2)
natEq 0 0 = Just Refl
natEq 0 (S _) = Nothing
natEq (S _) 0 = Nothing
natEq (S k) (S j) = (\x => cong S x) <$> natEq k j

-- 演習6
appRows : {ts1 : _} -> Row ts1 -> Row ts2 -> Row (ts1 ++ ts2)
appRows {ts1 = []}     Nil      y = y
appRows {ts1 = _ :: _} (h :: t) y = h :: appRows t y

zip : Table -> Table -> Maybe Table
zip (MkTable s1 m rs1) (MkTable s2 n rs2) =
  case natEq m n of
    Just Refl => Just $ MkTable _ _ (zipWith appRows rs1 rs2)
    Nothing   => Nothing

-- 1+1=2の証明(1 === 2でもいい)
onePlusOne : the Nat 1 + 1 = 2
onePlusOne = Refl

mapListLength : (f : a -> b) -> (as : List a) -> length as === length (map f as)
mapListLength f [] = Refl
mapListLength f (x :: xs) = cong S $ mapListLength f xs

-- 演習2-1
mapIdEither : (ea : Either e a) -> map Prelude.id ea === ea
mapIdEither (Left v) = Refl
mapIdEither (Right v) = Refl

mapIdList : (as : List a) -> map Prelude.id as === as
mapIdList [] = Refl
mapIdList (x :: xs) = cong (x ::) $ mapIdList xs