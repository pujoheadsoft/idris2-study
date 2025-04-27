module Law.Law

%default total

{-
  map id x = x などとしたとき、idは Prelude.id ではなく関数名として扱われる。
  回避するためには、Prelude.id と書くか、以下のように定義した大文字の識別子を使う。
  https://github.com/gemmaro/idris2-tutorial/blob/ja/translation/ja/src/Tutorial/Eq.md
-}
public export
Id : a -> a
Id = id

public export
Pure : Applicative f => a -> f a
Pure = pure

-- Functor則
public export
interface Functor f => FunctorLaw f where
  -- map id = id
  identity : {a : Type} -> (x : f a) -> map Id x = x

  -- map (f . g)  ==  map f . map g
  composition : {a, b, c : Type} -> (x : f a) -> (g : a -> b) -> (h : b -> c)
              -> map (h . g) x = ((map h) . (map g)) x

-- Applicative則
public export
interface Applicative f => ApplicativeLaw f where
  -- pure id <*> v = v
  aIdentity : {a : Type} -> (x : f a)
           -> pure Id <*> x = x

  -- pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
  aComposition : {a, b, c : Type} -> (u : f (b -> c)) -> (v : f (a -> b)) -> (w : f a)
              -> pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
  
  -- pure f <*> pure x = pure (f x)
  homomorphism : {a, b : Type} -> (g : a -> b) -> (x : a)
               -> pure g <*> pure x = pure {f} (g x)
  
  -- u <*> pure y = pure ($ y) <*> u
  interchangeProperty : {a, b : Type} -> (u : f (a -> b)) -> (y : a)
                     -> u <*> pure y = pure ($ y) <*> u

-- Monad則
public export
interface Monad m => MonadLaw m where
  leftIdentity : {a : Type} -> (x : a) -> (f : a -> m b)
               -> pure x >>= f = f x
  
  rightIdentity : {a : Type} -> (x : m a)
                -> x >>= Pure = x

  associativity : {a, b, c : Type} -> (x : m a) -> (f : a -> m b) -> (g : b -> m c)
                -> (x >>= f) >>= g = x >>= (\x' => f x' >>= g)

FunctorLaw Maybe where
  identity (Just _) = Refl
  identity Nothing = Refl

  composition (Just _) _ _ = Refl
  composition Nothing _ _ = Refl

ApplicativeLaw Maybe where
  aIdentity (Just _) = Refl
  aIdentity Nothing = Refl

  aComposition Nothing _ _ = Refl
  aComposition (Just _) Nothing _ = Refl
  aComposition (Just _) (Just _) Nothing = Refl
  aComposition (Just _) (Just _) (Just _) = Refl

  homomorphism _ _ = Refl

  interchangeProperty (Just _) _ = Refl
  interchangeProperty Nothing _ = Refl

MonadLaw Maybe where
  -- pure x >>= f = f x
  -- leftIdentity _ _ = Refl
  leftIdentity x f = Refl {x = f x} -- こう書ける

  rightIdentity (Just _) = Refl
  rightIdentity Nothing = Refl

  associativity (Just _) _ _ = Refl
  associativity Nothing _ _ = Refl
