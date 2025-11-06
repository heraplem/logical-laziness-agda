module Util where

-- For some reason, Curry doesn't have this function.
ap :: Monad m => m (a -> b) -> m a -> m b
ap m1 m2 = do
  x1 <- m1
  x2 <- m2
  return (x1 x2)