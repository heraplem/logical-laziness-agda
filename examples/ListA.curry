module ListA where

import T
import Tick

infixr 5 :~
data ListA a = NilA | (:~) (T a) (T (ListA a))

fromList :: [a] -> ListA a
fromList = foldr (\x xsA -> Thunk x :~ Thunk xsA) NilA

embedListA :: [T a] -> T (ListA a)
embedListA = foldr (\xA xsA -> fork (xA :~ xsA)) (fork NilA)
