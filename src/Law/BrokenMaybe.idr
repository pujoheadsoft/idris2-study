module Law.BrokenMaybe

import Law.Law

data BrokenMaybe : (ty : Type) -> Type where
  Nothing : BrokenMaybe ty
  Just : (x : ty) -> BrokenMaybe ty

Functor BrokenMaybe where
  map f (Just x) = Just (f x)
  map f Nothing  = Nothing

Applicative BrokenMaybe where
  pure a = Nothing -- JustではなくNothingを返すようにする
  Just f <*> Just a = Just (f a)
  _      <*> _      = Nothing

Monad BrokenMaybe where
  Nothing  >>= k = Nothing
  (Just x) >>= k = k x

MonadLaw BrokenMaybe where
  leftIdentity _ _ = ?l -- pureがNothingを返すようになると、証明が成り立たなくなる

  rightIdentity (Just _) = ?r
  rightIdentity Nothing = Refl

  associativity (Just _) _ _ = Refl
  associativity Nothing _ _ = Refl