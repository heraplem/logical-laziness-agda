module BankersQueue where

import Nat
import Tick
import T
import List

data Queue a = Queue
  { frontLen :: Nat
  , front :: T (List a)
  , backLen :: Nat
  , back :: T (List a)
  }
  deriving (Eq, Ord, Read, Show)

mkQueueM :: Nat -> T (List a) -> Nat -> T (List a) -> Tick (Queue a)
mkQueueM frontLen front backLen back = do
  tick
  if frontLen >= backLen
    then return (Queue frontLen front backLen back)
    else do
      back' <- withForced back reverseM
      front' <- withForced front (`toListM'` back')
      back'' <- nilM
      return (Queue (frontLen + backLen) front' 0 back'')

toListM :: Queue a -> Tick (T (List a))
toListM q = do
  tick
  withForced (front q) (`toListM'` back q)

toListM' :: List a -> T (List a) -> Tick (List a)
toListM' front back = do
  tick
  back' <- withForced back reverseM
  front `appendM` back'

emptyM :: Tick (Queue a)
emptyM = do
  front <- nilM
  back <- nilM
  return (Queue 0 front 0 back)

pushM :: a -> Queue a -> Tick (Queue a)
pushM x q = do
  tick
  back' <- thunk (return (x :~ back q))
  mkQueueM (frontLen q) (front q) (1 + backLen q) back'

popM :: Queue a -> Tick (Maybe (a, Queue a))
popM q = do
  tick
  front <- force (front q)
  case front of
    Nil -> return Nothing
    x :~ front' -> do
      q' <- mkQueueM (frontLen q - 1) front' (backLen q) (back q)
      return (Just (x, q'))