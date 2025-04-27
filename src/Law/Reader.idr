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
  (MkReader r2a) >>= f = MkReader $ \r => runReader (f (r2a r)) r

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

  すなわちReaderにおける左単位則とは
  MkReader (\r => runReader (f x) r) = f x ということになる。
  人間が見れば等しいと思えるが、Idrisはそうは思わない。
  なので leftIdentity = Refl のように書くとコンパイルエラーとなる。

-}


-- Readerレコードのイータ簡約の補題
-- reader : Reader r a に対して、 MkReader (runReader reader) と等しいことを証明する
lemmaReaderEtaReduction : (reader : Reader r a) -> MkReader (runReader reader) = reader
lemmaReaderEtaReduction (MkReader reader) = Refl { x = MkReader reader}
lemmaReaderEtaReduction (MkReader _) = Refl -- 省略した場合

-- transは (a = b) で (b = c) ならば (a = c) と証明を得る関数
-- そして trans p1 p2 としたとき以下のようにする
--   p1: MkReader x = MkReader (runReader (f v))
--   p2: MkReader (runReader (f v)) = f v
-- これにより 
proof_example : (v : a) -> (f : a -> Reader r b) -> MkReader (\r => runReader (f v) r) = f v
proof_example v f = trans (cong MkReader (Refl { x = runReader (f v) }) ) (lemmaReaderEtaReduction (f v))
-- trans (cong MkReader Refl) (lemmaReaderEtaReduction (f x))

MonadLaw (Reader r) where
  leftIdentity x f = ?hoge2
  rightIdentity (MkReader x) = Refl
  associativity (MkReader x) f g = ?y
