module Insert where

import T
import ListA
import Tick

-- -- Look up Steven's and Sergio's papers.
-- -- Look at Andrew's paper and see what it cites.

-- -- insertionSort :: Ord a => [a] -> [a]
-- -- insertionSort = foldr insert []

undefined = undefined

-- Return value wrapped in T.
insertA :: Ord a => T a -> T (ListA a) -> Tick (T (ListA a))
insertA xA xsA = do
  tick
  xs <- force xsA
  case xs of
    NilA -> return (embedListA [xA])
    _ -> undefined
    -- xA' :~ xsA' -> do
    --   x <- force xA
    --   x' <- force xA'
    --   if x <= x'
    --     then do
    --       xA''' <- thunk (return x')
    --       xsA'' <- thunk (return (xA''' :~ xsA'))
    --       xA'''' <- thunk (return x)
    --       xsA''' <- thunk (return (xA'''' :~ xsA''))
    --       return xsA'''
    --     else do
    --       -- Shortcut: we know that xA = Thunk x, so it doesn't matter what
    --       -- insertA demands.
    --       xsA'' <- insertA xA xsA'
    --       return (fork x' :~ xsA'')

insertionSort :: Ord a => T (ListA a) -> Tick (T (ListA a))
insertionSort xsA = do
  xs <- force xsA
  case xs of
    NilA -> thunk (return NilA)
    xA :~ xsA' -> do
      xsA'' <- insertionSort xsA'
      insertA xA xsA''


-- insertA :: Ord a => T a -> T (ListA a) -> Tick (ListA a)
-- insertA xA xsA = do
--   tick
--   x <- force xA
--   xs <- force xsA
--   case xs of
--     NilA -> return (fromList' [x])
--     xA' :~ xsA' -> do
--       x' <- force xA'
--       if x <= x'
--         then return (thunk' x :~ thunk' (thunk' x' :~ xsA'))
--         else do
--           xsA'' <- thunk (insertA xA xsA')
--           return (thunk' x' :~ xsA'')

-- insertionSortA :: Ord a => T (ListA a) -> Tick (ListA a)
-- insertionSortA xsA = do
--   tick
--   xs <- force xsA
--   case xs of
--     NilA -> thunk (return NilA)
--     xA :~ xsA' -> do
--       xsA'' <- thunk (insertionSortA xsA')
--       insertA xA xsA''

-- -- Variant in which the cost is a "fuel".
-- --
-- -- If it goes through, then the provided cost is an upper bound on the actual
-- -- cost.
-- --
-- -- What is Curry's resolution strategy?  Will it start at the "smallest" value
-- -- and work up?
-- insert' :: Ord a => Nat -> T a -> T (ListA a) -> T (ListA a)
-- insert' cost xA xsA = do
--   if cost == 0
--     then Undefined
--     else do
--       x <- force xA
--       xs <- force xsA
--       case xs of
--         NilA -> thunk (return (fromList' [x]))
--         xA' :~ xsA' -> do
--           x' <- force xA'
--           if x <= x'
--             then return (thunk' (thunk' x :~ thunk' (thunk' x' :~ xsA')))
--             else do
--               xsA'' <- insert' (cost - 1) xA xsA'
--               return (thunk' (thunk' x' :~ xsA''))

-- -- "Demand translation".
-- insert 1 xs =:= ([1, 2, 3], n) where xs n free

-- -- "Demand translation" using fuel.
-- insert' 1 xs n =:= [1, 2, 3] where xs n free
