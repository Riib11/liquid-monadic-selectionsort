module Refined.Data.ListOld where

-- ! this is false. what did I actually mean?
-- -- count_remove_contains_neq

-- {-@ automatic-instances count_remove_contains_neq @-}
-- {-@
-- count_remove_contains_neq ::
--   {xs:List | 0 < length xs} ->
--   {y:Int | contains xs y} ->
--   {z:Int | z /= y} ->
--   {count (remove xs y) z == count xs z}
-- @-}
-- count_remove_contains_neq :: List -> Int -> Int -> Proof
-- count_remove_contains_neq (Cons x Nil) y z = if y == x then trivial else trivial
-- count_remove_contains_neq (Cons x xs) y z =
--   -- GOAL: count (remove (Cons x xs) y) z == count (Cons x xs) z
--   if x == y
--     then -- GOAL: count xs z == count (Cons x xs) z
--       trivial
--     else -- GOAL: count (Cons x (remove xs y)) z == count (Cons x xs) z

--       if x == z
--         then -- GOAL: count (remove (Cons x xs) y) z == count (Cons x xs) z

--           trivial
--             `by` assume (count (remove (Cons x xs) y) z == count (Cons x xs) z)
--         else -- `by` count_remove_contains_neq xs y z
--         -- `by` assume (1 + count (remove xs y) z == 1 + count xs y)
--         -- GOAL: count (remove xs y) z == count xs z

--           trivial
--             `by` count_remove_contains_neq xs y z

-- trivial
--   `by` assume (count xs z == count (Cons y (remove xs y)) z)

-- trivial
--   `by` count_tl (Cons y (remove xs y)) z

-- `by` count_remove_contains_neq xs y z

-- -- swap

-- -- {-@ reflect swap @-}
-- -- {-@
-- -- swap ::
-- --   {i:Int | inBounds xs i} -> {i:Int | inBounds xs j} ->
-- --   {xs:List | 2 < length xs} ->
-- --   List
-- -- @-}
-- -- swap :: Int -> Int -> List -> List
-- -- swap i j (Cons x (Cons x' Nil)) =

-- -- permuted_cons

-- {-@ automatic-instances permuted_cons @-}
-- {-@
-- permuted_cons ::
--   {xs:List | 0 < length xs} ->
--   {ys:List | 0 < length ys && hd xs == hd ys}->
--   Permuted {tl xs} {tl ys} ->
--   Permuted {xs} {ys}
-- @-}
-- permuted_cons :: List -> List -> Permuted -> Permuted
-- permuted_cons xs ys p z =
--   if z == hd xs
--     then p z
--     else p z
