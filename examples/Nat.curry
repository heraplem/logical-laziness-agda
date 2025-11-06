module Nat where

data Nat = Z | S Nat
  deriving (Eq, Ord)

instance Num Nat where
  fromInt 0 = Z
  fromInt n | n > 0 = S (fromInt (n - 1))
