module List where

import T
import Nat
import Tick

infixr 5 :~
data List a = NilA | (:~) a (T (List a))
  deriving (Eq, Ord, Read, Show)

fromList :: [a] -> List a
fromList = foldr (\x xs -> x :~ Thunk xs) NilA

appendM :: List a -> T (List a) -> Tick (List a)
appendM xs ysT = do
  tick
  case xs of
    NilA -> force ysT
    x :~ xsT' -> do
      zsT <- withForced xsT' (`appendM` ysT)
      return (x :~ zsT)

reverseM :: List a -> Tick (List a)
reverseM = go NilA where
  go ys xs = do
    tick
    case xs of
      NilA -> return ys
      x :~ xsT' -> do
        ysT <- thunk (return ys)
        xs' <- force xsT'
        go (x :~ ysT) xs'
