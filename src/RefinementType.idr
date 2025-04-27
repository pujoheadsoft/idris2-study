{-
  https://github.com/stefan-hoeck/idris2-refined を使った例
-}
module RefinementType

import Control.Relation.ReflexiveClosure
import Control.Relation
-- import Language.Reflection.Pretty
import Language.Reflection.Util
import Derive.Prelude
import Derive.Refined
import Data.Refined.Bits32
import Data.Refined.Int8
import Data.Refined.String
import Derive.HDecEq

%default total
%language ElabReflection -- %runElabをするために必要

public export
MaxLen : Nat
MaxLen = 50

public export
0 IsAlias : String -> Type
IsAlias = Str $ Trimmed && Len (`LTE` MaxLen) && All PrintableAscii

public export
record Alias where
  constructor MkAlias
  value : String
  {auto 0 prf : IsAlias value}

%runElab derive "Alias" [Show, Eq, RefinedString]

hoeck : Alias
hoeck = "Stefan Hoeck"

data Weekday =
    Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday

%runElab derive "Weekday" [Show, Eq, Ord, HDecEq]

public export
record Percent where
  constructor MkPercent
  value : Bits32
  {auto 0 valid : value <= 100}

namespace Percent
  %runElab derive "Percent" [Show, Eq, Ord, RefinedInteger]

percent50 : Percent
percent50 = MkPercent 50