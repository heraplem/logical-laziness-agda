module Insert where

import T
import List
import Tick

-- pakcs :l Insert :a T
-- kics2 and curry2go both have Docker images

insertA :: Ord a => a -> T (List a) -> Tick (List a)
insertA x xsT = do
  tick
  xs <- force xsT
  case xs of
    NilA -> do
      xs' <- thunk (return NilA)
      return (x :~ xs')
    x' :~ xsT' ->
      if x <= x' then return (x :~ xsT)
      else do
        xsT'' <- thunk (insertA x xsT')
        return (x' :~ xsT'')

insertD :: (Data a, Ord a) => a -> List a -> Tick (List a)
insertD x ys | insertA x (Thunk xs) =:= Tick (ys, c) = Tick (xs, c)
  where xs, c free
