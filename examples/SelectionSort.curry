module SelectionSort where

import Util
import Tick
import T
import List

selectionSort :: Ord a => [a] -> [a]
selectionSort = go [] where
  go acc [] = acc
  go acc xs = go (x:acc) xs' where
    (i, x) = maxIndex xs
    (_, xs') = deleteAt i xs

selectionSortA' :: List a -> List a -> Tick (List a)
selectionSortA' acc xs = do
  tick
  fcase xs of
    Nil -> return acc
    x :~ xsA' -> do
