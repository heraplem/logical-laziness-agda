module Clairvoyance where

import T

newtype M a = M { runM :: [(a, Int)] }

instance Functor M where
  fmap f (M ps) = M [(f x, n) | (x, n) <- ps]

instance Applicative M where
  pure = return
  m1 <*> m2 = do
    x1 <- m1
    x2 <- m2
    return (x1 x2)

instance Monad M where
  return x = M $ return (x, 0)
  m >>= k = M $ do
    (x, n) <- runM m
    (x', n') <- runM (k x)
    return (x', n + n')