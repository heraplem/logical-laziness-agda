module Tick where

import Util
import Nat

newtype Tick a = Tick { runTick :: (a, Nat) }

instance Functor Tick where
  fmap f (Tick (x, n)) = Tick (f x, n)

instance Applicative Tick where
  pure = return
  (<*>) = ap

instance Monad Tick where
  return x = Tick (x, 0)
  m >>= k =
    let (x1, c1) = runTick m
        (x2, c2) = runTick (k x)
    in Tick (x2, c1 + c2)

tick :: Tick ()
tick = Tick ((), 1)