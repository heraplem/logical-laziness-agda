module T where

import Approx

data T a = Undefined | Thunk a
  deriving (Eq, Ord, Read, Show)

instance Functor T where
  fmap _ Undefined = Undefined
  fmap f (Thunk x) = Thunk (f x)

instance Approx a => Approx (T a) where
  Undefined <~ _         = True
  Thunk _   <~ Undefined = False
  Thunk x   <~ Thunk y   = x <~ y

  approx _         = Undefined
  approx (Thunk x) = Thunk (approx x)

-- In fact, only needs "Pointed", not Applicative.
thunk :: Applicative f => f a -> f (T a)
thunk m = pure Undefined ? fmap Thunk m

-- Suspiciously similar...
transpose :: Applicative f => T (f a) -> f (T a)
transpose Undefined = pure Undefined
transpose (Thunk m) = fmap Thunk m

forcing :: T a -> (a -> b) -> b
forcing (Thunk v) f = f v

fromThunk :: T a -> a
fromThunk = (`forcing` id)

-- In fact, only needs "Pointed", not Applicative.
force :: Applicative f => T a -> f a
force t = forcing t pure

under :: Applicative f => T a -> (a -> f b) -> f (T b)
under t k = thunk (forcing t k)
