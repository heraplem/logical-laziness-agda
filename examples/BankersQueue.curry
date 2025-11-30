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
      front' <- withForced front (`appendM` back')
      back'' <- thunk (return NilA)
      return (Queue (frontLen + backLen) front' 0 back'')

emptyM :: Tick (Queue a)
emptyM = do
  front <- thunk (return NilA)
  back <- thunk (return NilA)
  return (Queue 0 front 0 back)

pushM :: a -> Queue a -> Tick (Queue a)
pushM x q = do
  tick
  back' <- thunk (return (x :~ back q))
  mkQueueM (frontLen q) (front q) (S (backLen q)) back'

popM :: Queue a -> Tick (Maybe (a, Queue a))
popM q = do
  tick
  front <- force (front q)
  case front of
    NilA -> return Nothing
    x :~ front' -> do
      q' <- mkQueueM (frontLen q - 1) front' (backLen q) (back q)
      return (Just (x, q'))