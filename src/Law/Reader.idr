module Law.Reader

-- import Control.Function.FunExt
import Law.Law

%default total

record Reader (r : Type) (a : Type) where
  constructor MkReader
  runReader : r -> a

Functor (Reader r) where
  -- map : (a -> b) -> Reader r a -> Reader r b
  map f (MkReader r2a) = MkReader (\r => f $ r2a r)

Applicative (Reader r) where
  -- pure : a -> Reader r a
  pure a = MkReader (\r => a)
  MkReader f <*> MkReader x = MkReader (\e' => f e' (x e'))

Monad (Reader r) where
  -- m a -> (a -> m b) -> m b
  -- Reader r a -> (a -> Reader r b) -> Reader r b
  -- (MkReader r2a) >>= f = MkReader $ \r => do
  --   let
  --     a = r2a r
  --     (MkReader r2b) = f a
  --   r2b r
  x >>= f = MkReader $ \env => runReader (f (runReader x env)) env

FunctorLaw (Reader r) where
  identity (MkReader x) = Refl
  composition (MkReader x) f g = Refl

ApplicativeLaw (Reader r) where
  aIdentity (MkReader x) = Refl
  aComposition (MkReader u) (MkReader v) (MkReader w) = Refl
  homomorphism f x = Refl
  interchangeProperty (MkReader u) y = Refl


{-
  左単位則を証明する
  左単位則は、pure x >>= f = f x というもの。
  pure や >>= を Reader の文脈で考えると
  pure x は MkReader (\r => x)となる。
  そこから更に >>= f を適用すると
      MkReader (\r => x) >>= f
    = MkReader (\r => runReader (f x) r) となる。
  すなわち
    MkReader (\r => runReader (f x) r) = f x
  という等式を証明すればよい。

  しかし v : a, f : a -> Reader r b
  としたときIdrisは等式
    MkReader (\r => runReader (f v) r) = f v
  を自動で証明できない。

  なぜならば、Idrisの型検査器は変数項を含む等価性、特に項の簡約順序に依存するものは定義的等価と見なされないことがあり、
  この場合 f v が変数項であるため。

  そこで仕方ないので自前で証明する。
  アプローチとして、等式 MkReader (\r => runReader (f v) r) = f v を
  定義的な等価性として自動的に扱えない部分と、定義的な等価性として扱える部分に分解し、それぞれを証明してから、
  それらを組み合わせて最終的な証明を得る。

  証明は2つの部分に分けられる。
  1. MkReader (\r => runReader (f v) r) = MkReader (runReader (f v)) という等式の証明
  2. MkReader (runReader (f v)) = f v という等式の証明
  この2つの等式を trans で組み合わせることで、最終的な証明(もともと証明したかった等式の証明)
    MkReader (\r => runReader (f v) r) = f v
  を得る。
  ※transは (a = b) で (b = c) ならば (a = c) と証明を得る関数

  詳しくみていく
  1. MkReader (\r => runReader (f v) r) = MkReader (runReader (f v)) の証明
  まず MkReader (\r => runReader (f v) r) = f v の MkReader の引数の
    (\r => runReader (f v) r)
  に着目する。
  このラムダ式 (\r => runReader (f v) r) は、ラムダ計算のη簡約によって runReader (f v) と定義的に等しい。
  (IdrisとかHaskellとかで、func x = f x が func = f と書けるってことだね)
  したがって、(\r => runReader (f v) r) = runReader (f v) は定義的な等価性であり、Refl で証明できる。
  Refl { x = runReader (f v) } がこの等価性の証明である。
  続いてこの証明と cong MkReader により
  MkReader (\r => runReader (f v) r) = MkReader (runReader (f v)) という等式の証明が得られる。
  (cong f (a = b) は f a = f b という等式の証明を得る関数だから、↑の等式になる)
  これで1つ目の等式の証明が得られた。

  2. MkReader (runReader (f v)) = f v の証明
  既に述べた通り、変数項が含まれる場合は定義的等価性として扱えないため、f vの結果を受ける別の関数(証明)を用意する。
  ここでは reader : Reader r a に対して、 MkReader (runReader reader) と reader が等しいことを証明する。
-}
-- ラムダ式のイータ簡約の証明を、MkReader コンストラクタの下で持ち上げる
lemma : (v : a) -> (f : a -> Reader r b) -> MkReader (\r => runReader (f v) r) = MkReader (runReader (f v))
lemma v f = cong MkReader (Refl { x = runReader (f v) })

-- Readerレコードのイータ簡約の補題
-- reader : Reader r a に対して、 MkReader (runReader reader) と等しいことを証明する
-- これはReflで証明できる。
lemmaReaderEtaReduction : (reader : Reader r a) -> MkReader (runReader reader) = reader
lemmaReaderEtaReduction (MkReader reader) = Refl { x = MkReader reader}
-- lemmaReaderEtaReduction (MkReader _) = Refl -- 省略した場合

proof_leftIdentity : (v : a) -> (f : a -> Reader r b) -> MkReader (\r => runReader (f v) r) = f v
proof_leftIdentity v f = trans (lemma v f) (lemmaReaderEtaReduction (f v))

proofAssociativity : (x : Reader r a)
    -> (f : (a -> Reader r b))
    -> (g : (b -> Reader r c))
    -> (x >>= f) >>= g = x >>= (\x' => f x' >>= g)
proofAssociativity x f g = ?holeAssociativity

MonadLaw (Reader r) where
  leftIdentity x f = proof_leftIdentity x f
  rightIdentity (MkReader r2a) = Refl
  -- (x >>= f) >>= g = x >>= (\x' => f x' >>= g)
  associativity x f g = ?y
