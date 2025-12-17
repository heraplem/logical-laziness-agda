module Approx where

infix 4 <~
class Data a => Approx a where
  (<~) :: a -> a -> Bool

  -- Nondeterministically generate approximations.
  approx :: a -> a
  approx x | y <~ x = y
    where y free

instance Approx () where
  _ <~ _ = True
  approx = const ()

instance Approx Int where
  (<~) = (==)
  approx = id

instance Approx a => Approx [a] where
  []       <~ []     = True
  (x : xs) <~ (y : ys) = x <~ y && xs <~ ys

  approx []       = []
  approx (x : xs) = approx x : approx xs
