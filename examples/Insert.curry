module Insert where

import Approx
import T
import List
import Tick

-- pakcs :l Insert :a T
-- kics2 and curry2go both have Docker images

insert :: Ord a => a -> [a] -> [a]
insert x [] = [x]
insert x ys@(y : ys')
  | x <= y    = x : ys
  | otherwise = y : insert x ys'

insertionSort :: Ord a => [a] -> [a]
insertionSort = foldr insert []

insertA :: Ord a => a -> List a -> Tick (List a)
insertA x ys = do
  tick
  case ys of
    NilA -> do
      ys' <- thunk (return NilA)
      return (x :~ ys')
    y :~ ysT' ->
      if x <= y then do
        ysT <- thunk (return ys)
        return (x :~ ysT)
      else do
        ysT'' <- withForced ysT' (insertA x)
        return (y :~ ysT'')

insertD :: (Data a, Ord a, Approx a) => a -> List a -> List a -> Tick (a, List a)
insertD x xs ysD |  xD <~ x
                 && xsD <~ xs
                 && insertA xD xsD =:= Tick (ysD, c)
                 =  Tick ((xD, xsD), c)
  where xD, xsD, c free
