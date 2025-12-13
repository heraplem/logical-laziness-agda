module InsertionSort where

import Control.Monad

import Approx
import T
import Tick
import List

--------------------
-- Insertion sort --
--------------------

-- Pure

insert :: Ord a => a -> [a] -> [a]
insert x [] = [x]
insert x ys@(y : ys')
  | x <= y    = x : ys
  | otherwise = y : insert x ys'

insertionSort :: Ord a => [a] -> [a]
insertionSort = foldr insert []

-- Clairvoyance

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
        ysT'' <- with ysT' (insertC x)
        return (y :~ ysT'')

insertionSortC :: Ord a => List a -> Tick (List a)
insertionSortC xs = do
  tick
  fcase xs of
    Nil -> return Nil
    x :~ xsT' -> do
      ysT' <- with xsT' insertionSortC
      ys' <- force ysT'
      insertC x ys'

-- Demand (constraints)

insertD :: (Ord a, Approx a) => a -> List a -> List a -> Tick (a, List a)
insertD x xs ysD |  xD  <~ x
                 && xsD <~ xs
                 && insertC xD xsD =:= Tick (ysD, c)
                 =  Tick ((xD, xsD), c)
  where xD, xsD, c free

insertionSortD :: (Ord a, Approx a) => List a -> List a -> Tick (List a)
insertionSortD xs ysD |  xsD <~ xs
                      && insertionSortC xsD =:= Tick (ysD, c)
                      =  Tick (xsD, c)
  where xsD, c free

-- Demand (generators)

insertDG :: (Ord a, Approx a) => a -> List a -> List a -> Tick (a, List a)
insertDG x xs ysD | insertC xD xsD =:= Tick (ysD, c)
                  = Tick ((xD, xsD), c)
  where xD = approx x
        xsD = approx xs
        c free

insertionSortDG :: (Ord a, Approx a) => List a -> List a -> Tick (List a)
insertionSortDG xs ysD | insertionSortC xsD =:= Tick (ysD, c)
                       = Tick (xsD, c)
  where xsD = approx xs
        c free

-- Demand (manual)

insertDM :: Ord a => a -> [a] -> List a -> Tick (List a)
insertDM x ys zsD = do
  tick
  case (ys, zsD) of
    ([], _) -> return Nil
    (y : ys', zD :~ zsTD') ->
       if y <= x
       then do
         ysTD' <- transpose (insertDM x ys' <$> zsTD')
         return (y :~ ysTD')
       else return (fromThunk zsTD')

insertionSortDM :: Ord a => [a] -> List a -> Tick (List a)
insertionSortDM xs ysD = do
  tick
  case xs of
    [] -> return Nil
    x : xs' -> do
      let ys' = insertionSort xs'
      ysD' <- insertDM x ys' ysD
      xsD' <- insertionSortDM xs' ysD'
      return (x :~ Thunk xsD')

------------------------
-- n-minimum elements --
------------------------

-- Clairvoyance
nminC :: Ord a => Int -> T (List a) -> Tick (List a)
nminC n xsT = takeC n =<< with xsT insertionSortC

-- Demand (constraints)
nminD :: (Ord a, Approx a) => Int -> T (List a) -> List a -> Tick (T (List a))
nminD n xsT ysTD |  xsTD <~ xsT
                 && nminC n xsTD =:= Tick (ysTD, c)
                 =  Tick (xsTD, c)
  where xsTD, c free

-- Demand (generators)
nminDG :: (Ord a, Approx a) => Int -> T (List a) -> List a -> Tick (T (List a))
nminDG n xsT ysTD | nminC n xsTD =:= Tick (ysTD, c)
                  = Tick (xsTD, c)
  where xsTD = approx xsT
        c free

-- Demand (manual)
nminDM :: Ord a => Int -> [a] -> T (List a) -> Tick (T (List a))
nminDM n xs ysTD = do
  let zs = insertionSort xs
  zsTD <- takeDM n zs ysTD
  transpose (insertionSortDM xs <$> zsTD)
