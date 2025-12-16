module BankersQueue where

import Tick
import T
import List

data Queue a = Queue
  { frontLen :: Int
  , front :: T (List a)
  , backLen :: Int
  , back :: T (List a)
  }
  deriving (Eq, Ord, Read, Show)

mkQueueC :: Int -> T (List a) -> Int -> T (List a) -> Tick (Queue a)
mkQueueC frontLen front backLen back = do
  tick
  if frontLen >= backLen
    then return (Queue frontLen front backLen back)
    else do
      back' <- with back reverseC
      front' <- with front (`toListC'` back')
      back'' <- nilC
      return (Queue (frontLen + backLen) front' 0 back'')

toListC :: Queue a -> Tick (T (List a))
toListC q = do
  tick
  withForced (front q) (`toListC'` back q)

toListC' :: List a -> T (List a) -> Tick (List a)
toListC' front back = do
  tick
  back' <- with back reverseM
  front `appendC` back'

emptyC :: Tick (Queue a)
emptyC = do
  front <- nilC
  back <- nilC
  return (Queue 0 front 0 back)

pushC :: a -> Queue a -> Tick (Queue a)
pushC x q = do
  tick
  back' <- thunk (return (x :~ back q))
  mkQueueC (frontLen q) (front q) (backLen q + 1) back'

popC :: Queue a -> Tick (Maybe (a, Queue a))
popC q = do
  tick
  front <- force (front q)
  case front of
    Nil -> return Nothing
    x :~ front' -> do
      q' <- mkQueueC (frontLen q - 1) front' (backLen q) (back q)
      return (Just (x, q'))
