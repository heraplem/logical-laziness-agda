module Approx where

infix 4 <~
class Approx a where
  (<~) :: a -> a -> Bool

instance Approx Int where
  (<~) = (==)