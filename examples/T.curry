module T where

data T a = Thunk a | Undefined
  deriving (Eq, Ord, Read, Show)

-- XXX Should probably only need two of these at most.
-- And need better names.

fork :: a -> T a
fork x = Thunk x ? Undefined

-- -- In fact, only needs "Pointed", not Applicative.
thunk :: Applicative f => f a -> f (T a)
thunk m = fmap Thunk m ? pure Undefined

forcing :: T a -> (a -> b) -> b
forcing (Thunk v) f = f v

-- In fact, only needs "Pointed", not Applicative.
force :: Applicative f => T a -> f a
force t = forcing t pure