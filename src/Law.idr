module Law

%default total

Pure : Applicative f => a -> f a
Pure = pure

interface Monad m => MonadLaw m where
  leftIdentity : {a : Type} -> (x : a) -> (f : a -> m b)
               -> pure x >>= f = f x
  
  rightIdentity : {a : Type} -> (x : m a)
                -> x >>= Pure = x

  associativity : {a, b, c : Type} -> (x : m a) -> (f : a -> m b) -> (g : b -> m c)
                -> (x >>= f) >>= g = x >>= (\x' => f x' >>= g)

MonadLaw Maybe where
  leftIdentity x f = Refl

  rightIdentity (Just x) = Refl
  rightIdentity Nothing = Refl

  associativity (Just x) f g = Refl
  associativity Nothing f g = Refl