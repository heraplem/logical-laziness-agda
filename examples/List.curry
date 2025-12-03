module List where

import Approx
import T
import Nat
import Tick

infixr 5 :~
data List a = NilA | (:~) a (T (List a))
  deriving (Eq, Ord, Read, Show)

instance Approx a => Approx (List a) where
  NilA      <~ NilA      = True
  NilA      <~ _ :~ _    = False
  _ :~ _    <~ NilA      = False
  x :~ xsT' <~ y :~ ysT' = x <~ y && xsT' <~ ysT'

fromList :: [a] -> List a
fromList = foldr (\x xs -> x :~ Thunk xs) NilA

takeM :: Nat -> List a -> List a
takeM n xs = do
  tick
  fcase (n, xs) of
    (Z  , NilA     ) -> return NilA
    (Z  , _ :~ _   ) -> return NilA
    (S _, NilA     ) -> return NilA
    (S n, x :~ xsT ) -> do
      xsT' <- withForced xsT' (takeM n)
      return (x :~ xsT')

appendM :: List a -> T (List a) -> Tick (List a)
appendM xs ysT = do
  tick
  fcase xs of
    NilA -> force ysT
    x :~ xsT' -> do
      zsT <- withForced xsT' (`appendM` ysT)
      return (x :~ zsT)

reverseM :: List a -> Tick (List a)
reverseM = go NilA where
  go ys xs = do
    tick
    fcase xs of
      NilA -> return ys
      x :~ xsT' -> do
        ysT <- thunk (return ys)
        xs' <- force xsT'
        go (x :~ ysT) xs'
