module Nat where

data Nat = Z | S Nat
  deriving (Eq, Ord, Read, Show)

instance Num Nat where
  Z + n = n
  S m + n = S (m + n)

  fromInt 0 = Z
  fromInt n | n > 0 = S (fromInt (n - 1))
