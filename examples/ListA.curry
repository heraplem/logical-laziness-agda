module ListA where

import T
import Tick

infixr 5 :~
data ListA a = NilA | (:~) a (T (ListA a))
  deriving (Eq, Ord, Read, Show)

fromList :: [a] -> ListA a
fromList = foldr (\x xs -> x :~ Thunk xs) NilA
