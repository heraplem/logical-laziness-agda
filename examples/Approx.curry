module Approx where

class Approx a where
  (<~) :: a -> a -> Bool