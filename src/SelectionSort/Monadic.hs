module SelectionSort.Monadic where

import Imperative.Array
import Refined.Data.Int
import Refined.Data.List (List)

-- -- run selection sort

-- runSort :: List -> List
-- runSort xs = case runArr sort xs of
--   Just (_, xs') -> xs'
--   Nothing -> xs -- TODO: what to do here... shouldn't happen, so doesn't matter?

-- -- selection sort

-- sort :: Arr ()
-- sort = getLng `bnd` \l -> sort_aux 0 l

-- -- selection sort starting from `i
-- {-@
-- sort_aux :: i:Int -> l:Int -> Arr () / [l - i]
-- @-}
-- sort_aux :: Int -> Int -> Arr ()
-- sort_aux i l =
--   if l - i <= 1
--     then ret ()
--     else select i l `thn` sort_aux (add1 i) l

-- -- select

-- {-@
-- select :: i:Int -> l:Int -> Arr () / [l - i]
-- @-}
-- select :: Int -> Int -> Arr ()
-- select i l =
--   if l - i <= 1
--     then ret ()
--     else
--       red i `bnd` \x1 ->
--         red (add1 i) `bnd` \x2 ->
--           if x1 <= x2
--             then
--               swap i (add1 i)
--                 `thn` select (add1 i) l
--                 `thn` swap i (add1 i)
--             else
--               select (add1 i) l
--                 `thn` swap i (add1 i)
