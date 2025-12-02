module Nat where

import Approx

data Nat = Z | S Nat
  deriving (Eq, Ord, Read, Show)

instance Num Nat where
  Z   + n = n
  S m + n = S (m + n)

  m   - Z   = m
  S m - S n = m - n

  fromInt n = case n `compare` 0 of
    EQ -> Z
    GT -> S (fromInt (n - 1))

instance Approx Nat where
  (<~) = (==)