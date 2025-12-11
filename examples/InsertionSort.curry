module InsertionSort where

import Control.Monad

import Approx
import T
import Nat
import Tick
import List

-- pakcs :l Insert :a T
-- kics2 and curry2go both have Docker images

insert :: Ord a => a -> [a] -> [a]
insert x [] = [x]
insert x ys@(y : ys')
  | x <= y    = x : ys
  | otherwise = y : insert x ys'

insertionSort :: Ord a => [a] -> [a]
insertionSort = foldr insert []

insertC :: Ord a => a -> List a -> Tick (List a)
insertC x ys = do
  tick
  fcase ys of
    Nil -> do
      ys' <- nilC
      return (x :~ ys')
    y :~ ysT' ->
      if x <= y then do
        ysT <- thunk (return ys)
        return (x :~ ysT)
      else do
        ysT'' <- under ysT' (insertC x)
        return (y :~ ysT'')

-- insertC :: Ord a => a -> List a -> Tick (List a)
-- insertC x xs = do
--   tick
--   fcase xs of
--     y :~ ys ->
--       if x >= y then
--         forcing ys (\ys' -> do
--           t <- thunk (insertC x ys')
--           return (y :~ t))
--       else return (x :~ Thunk (y :~ ys))
--     Nil -> return (x :~ Thunk Nil)

insertD :: (Ord a, Data a, Approx a) => a -> List a -> List a -> Tick (a, List a)
insertD x xs ysD |  xD  <~ x
                 && xsD <~ xs
                 && insertC xD xsD =:= Tick (ysD, c)
                 =  Tick ((xD, xsD), c)
  where xD, xsD, c free

-- insertionSortC' :: Ord a => T (List a) -> Tick (T (List a))
-- insertionSortC' xsT = under xsT $ \xs -> do
--   tick
--   fcase xs of
--     Nil -> return Nil
--     x :~ xsT' -> do
--       ysT' <- insertionSortC' xsT'
--       ys' <- force ysT'
--       insertC x ys'

-- insertionSortC :: Ord a => List a -> Tick (List a)
-- insertionSortC xs = do
--   ysT <- insertionSortC' (Thunk xs)
--   force ysT

foldrC :: (a -> T b -> Tick b) -> Tick b -> List a -> Tick b
foldrC f = foldrA (\aT b -> transpose b >>= f aT)

-- insertionSortC :: Ord a => List a -> Tick (List a)
-- insertionSortC = foldrC (\x xsT -> tick >> forcing xsT (insertC x)) (return Nil)

-- insertionSort [

insertionSortC :: Ord a => List a -> Tick (List a)
insertionSortC xs = do
  tick
  fcase xs of
    Nil -> return Nil
    x :~ xsT' -> do
      ysT' <- under xsT' insertionSortC
      ys' <- force ysT'
      insertC x ys'

insertionSortD :: (Ord a, Data a, Approx a) => List a -> List a -> Tick (List a)
insertionSortD xs ysD |  xsD <~ xs
                      && insertionSortC xsD =:= Tick (ysD, c)
                      =  Tick (xsD, c)
  where xsD, c free

firstC :: Ord a => Nat -> T (List a) -> Tick (List a)
firstC n xsT = do
  tick
  ysT <- under xsT insertionSortC
  takeC n ysT

-- firstD :: (Ord a, Data a, Approx a) => Nat -> T (List a) -> T (List a) -> Tick (T (List a))
-- firstD n xs ysD |  xsD <~ xs
--                 && firstC n xsD =:= Tick (ysD, c)
--                 =  Tick (xsD, c)
--   where xsD, c free