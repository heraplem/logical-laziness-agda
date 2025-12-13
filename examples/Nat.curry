module Nat where

import Approx

data Nat = Z | S Nat
  deriving (Eq, Ord, Read, Show)

instance Num Nat where
  Z   + n = n
  S m + n = S (m + n)

  m   - Z   = m
  S m - S n = m - n

  Z   * _ = Z
  S m * n = n + m * n

  abs n = n

  signum Z     = 0
  signum (S _) = 1

  fromInt n = case n `compare` 0 of
    EQ -> Z
    GT -> S (fromInt (n - 1))

instance Enum Nat where
  succ = S

  pred Z     = error "bad argument"
  pred (S n) = n

  toEnum = fromInt

  fromEnum Z     = 0
  fromEnum (S n) = 1 + fromEnum n

instance Approx Nat where
  (<~) = (==)
