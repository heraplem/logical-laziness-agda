module Util where

-- For some reason, Curry doesn't have this function.
ap :: Monad m => m (a -> b) -> m a -> m b
ap m1 m2 = do
  f <- m1
  x <- m2
  return (f x)