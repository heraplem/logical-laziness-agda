module Approx where

infix 4 <~
class Data a => Approx a where
  (<~) :: a -> a -> Bool

  -- Nondeterministically generate approximations.
  approx :: a -> a
  approx x | y <~ x = y
    where y free

instance Approx Int where
  (<~) = (==)
  approx = id
