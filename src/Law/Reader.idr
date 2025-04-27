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


-- Readerレコードのイータ簡約の補題
-- reader : Reader r a に対して、 MkReader (runReader reader) と等しいことを証明する
lemmaReaderEtaReduction : (reader : Reader r a) -> MkReader (runReader reader) = reader
lemmaReaderEtaReduction (MkReader _) = Refl

proof_example : (f : a -> Reader r b) -> (x : a) -> MkReader (\r => runReader (f x) r) = f x
proof_example f x = trans (cong MkReader Refl) (lemmaReaderEtaReduction (f x))


MonadLaw (Reader r) where
  leftIdentity x f = proof_example f x
  rightIdentity (MkReader x) = Refl
  associativity (MkReader x) f g = ?y
