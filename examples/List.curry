module List where

import Approx
import T
import Nat
import Tick

infixr 5 :~
data List a = Nil | (:~) a (T (List a))
  deriving (Eq, Ord, Read, Show)

foldrA :: (a -> T b -> b) -> b -> List a -> b
foldrA _ e Nil         = e
foldrA f e (x :~ xsT') = x `f` (foldrA f e <$> xsT')

instance Approx a => Approx (List a) where
  Nil         <~ Nil         = True
  Nil         <~ (_ :~ _   ) = False
  (_ :~ _   ) <~ Nil         = False
  (x :~ xsT') <~ (y :~ ysT') = x <~ y && xsT' <~ ysT'

fromList :: [a] -> List a
fromList = foldr (\x xs -> x :~ (Undefined ? Thunk xs)) Nil

nilC :: Tick (T (List a))
nilC = do
  tick
  thunk (return Nil)

undefined :: a
undefined = undefined

takeC :: Nat -> T (List a) -> Tick (List a)
takeC n xsT = do
  tick
  fcase n of
    Z -> return Nil
    S n' -> do
      xs <- force xsT
      fcase xs of
        Nil -> return Nil
        x :~ xsT' -> do
          ysT' <- thunk (takeC n' xsT')
          return (x :~ ysT')

takeD :: (Approx a, Data a) => Nat -> T (List a) -> List a -> Tick (T (List a))
takeD n xsT ysD |  xsTD <~ xsT
                && takeC n xsTD =:= Tick (ysD, c)
                =  Tick (xsTD, c)
  where xsTD, c free

appendC :: List a -> T (List a) -> Tick (List a)
appendC xs ysT = do
  tick
  fcase xs of
    Nil -> force ysT
    x :~ xsT' -> do
      zsT <- under xsT' (`appendC` ysT)
      return (x :~ zsT)

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

takeAppendC :: Nat -> List a -> T (List a) -> Tick (List a)
takeAppendC n xs1 xs2T = do
  ysT <- thunk (appendC xs1 xs2T)
  takeC n ysT

takeAppendD :: (Approx a, Data a) => Nat -> List a -> T (List a) -> List a -> Tick (List a, T (List a))
takeAppendD n xs ysT zsD |  xsD <~ xs
                         && ysTD <~ ysT
                         && takeAppendC n xsD ysTD =:= Tick (zsD, c)
                         =  Tick ((xsD, ysTD), c)
  where xsD, ysTD, c free