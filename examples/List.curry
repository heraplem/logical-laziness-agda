module List where

import Approx
import T
import Tick

infixr 5 :~
data List a = Nil | (:~) a (T (List a))
  deriving (Eq, Ord, Read, Show)

foldrA :: (a -> T b -> b) -> b -> List a -> b
foldrA _ e Nil         = e
foldrA f e (x :~ xsT') = x `f` (foldrA f e <$> xsT')

foldrC :: (a -> T b -> Tick b) -> Tick b -> List a -> Tick b
foldrC f = foldrA (\aT b -> transpose b >>= f aT)

instance Approx a => Approx (List a) where
  Nil         <~ Nil         = True
  Nil         <~ (_ :~ _   ) = False
  (_ :~ _   ) <~ Nil         = False
  (x :~ xsT') <~ (y :~ ysT') = x <~ y && xsT' <~ ysT'

  approx Nil         = Nil
  approx (x :~ xsT') = approx x :~ approx xsT'

fromList :: [a] -> List a
fromList = foldr (\x xs -> x :~ Thunk xs) Nil

nilC :: Tick (T (List a))
nilC = thunk (return Nil)

----------
-- take --
----------

-- Clairvoyance
takeC :: Int -> T (List a) -> Tick (List a)
takeC n xsT = do
  tick
  fcase n `compare` 0 of
    EQ -> return Nil
    GT -> do
      let n' = n - 1
      xs <- force xsT
      fcase xs of
        Nil -> return Nil
        x :~ xsT' -> do
          ysT' <- thunk (takeC n' xsT')
          return (x :~ ysT')

-- Demand (constraints)
takeD :: Approx a => Int -> T (List a) -> List a -> Tick (T (List a))
takeD n xsT ysD |  xsTD <~ xsT
                && takeC n xsTD =:= Tick (ysD, c)
                =  Tick (xsTD, c)
  where xsTD, c free

-- Demand (generators)
takeDG :: Approx a => Int -> T (List a) -> List a -> Tick (T (List a))
takeDG n xsT ysD | takeC n xsTD =:= Tick (ysD, c)
                 = Tick (xsTD, c)
  where xsTD = approx xsT
        c free

-- Demand (hand-written)
takeDM :: Int -> [a] -> T (List a) -> Tick (T (List a))
takeDM n xs ysTD = do
  tick
  case n `compare` 0 of
    EQ -> return Undefined
    GT ->
      let n' = n - 1
      in case (xs, ysTD) of
        ([], _) -> return (Thunk Nil)
        (x : xs', Thunk (y :~ ysTD')) -> do
          xsTD' <- takeDM n' xs' ysTD'
          return (Thunk (y :~ xsTD'))

------------
-- append --
------------

-- Clairvoyance
appendC :: List a -> T (List a) -> Tick (List a)
appendC xs ysT = do
  tick
  fcase xs of
    Nil -> force ysT
    x :~ xsT' -> do
      zsT <- with xsT' (`appendC` ysT)
      return (x :~ zsT)

-----------------
-- take-append --
-----------------

-- Clairvoyance
takeAppendC :: Int -> List a -> T (List a) -> Tick (List a)
takeAppendC n xs1 xs2T = do
  ysT <- thunk (appendC xs1 xs2T)
  takeC n ysT

-- Demand (constraints)
takeAppendD :: Approx a => Int -> List a -> T (List a) -> List a -> Tick (List a, T (List a))
takeAppendD n xs ysT zsD |  xsD <~ xs
                         && ysTD <~ ysT
                         && takeAppendC n xsD ysTD =:= Tick (zsD, c)
                         =  Tick ((xsD, ysTD), c)
  where xsD, ysTD, c free

-------------
-- reverse --
-------------

-- Clairvoyance
reverseC :: List a -> Tick (List a)
reverseC = go Nil where
  go ys xs = do
    tick
    fcase xs of
      Nil -> return ys
      x :~ xsT' -> do
        ysT <- thunk (return ys)
        xs' <- force xsT'
        go (x :~ ysT) xs'
