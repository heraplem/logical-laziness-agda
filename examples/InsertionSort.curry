module InsertionSort where

import Control.Monad

import Approx
import T
import Nat
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
        ysT'' <- under ysT' (insertC x)
        return (y :~ ysT'')

insertionSortC :: Ord a => List a -> Tick (List a)
insertionSortC xs = do
  tick
  fcase xs of
    Nil -> return Nil
    x :~ xsT' -> do
      ysT' <- under xsT' insertionSortC
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

---------------------
-- First (n-least) --
---------------------

-- Clairvoyance
firstC :: Ord a => Nat -> T (List a) -> Tick (List a)
firstC n xsT = takeC n =<< under xsT insertionSortC

-- Demand (constraints)
firstD :: (Ord a, Approx a) => Nat -> T (List a) -> List a -> Tick (T (List a))
firstD n xsT ysTD |  xsTD <~ xsT
                  && firstC n xsTD =:= Tick (ysTD, c)
                 =  Tick (xsTD, c)
  where xsTD, c free

-- Demand (generators)
firstDG :: (Ord a, Approx a) => Nat -> T (List a) -> List a -> Tick (T (List a))
firstDG n xsT ysTD | firstC n xsTD =:= Tick (ysTD, c)
                   = Tick (xsTD, c)
  where xsTD = approx xsT
        c free

-- Demand (manual)
firstDM :: Ord a => Nat -> [a] -> T (List a) -> Tick (T (List a))
firstDM n xs ysTD = do
  let zs = insertionSort xs
  zsTD <- takeD' n zs ysTD
  transpose (insertionSortDM xs <$> zsT)
