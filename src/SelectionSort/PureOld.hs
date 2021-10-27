module SelectionSort.PureOld where

-- -- sort

-- {-@ reflect sort @-}
-- {-@ automatic-instances sort @-}
-- sort :: List -> List
-- sort Nil = Nil
-- sort (Cons x Nil) = Cons x Nil
-- sort xs =
--   let m = minimum xs `by` minimum_contains xs in
--   Cons m (sort (without xs m `by` without_length xs m))

-- {-@ automatic-instances sort_sorted @-}
-- {-@
-- sort_sorted :: xs:List -> {sorted (sort xs)}
-- @-}
-- sort_sorted :: List -> Proof
-- sort_sorted Nil = undefined -- * PASSES: trivial
-- sort_sorted (Cons x Nil) = undefined -- * PASSES: trivial
-- sort_sorted (Cons x xs) =
--   let m   = minimum xs `by` minimum_contains xs
--       xs' = without xs m `by` without_length xs m
--       t   = sort xs'
--               `by` sort_permuted xs'
--               `by` length_permuted xs' t
--               `by` assume_permuted (without xs' (minimum xs')) t
--       sort_xs = sort xs -- Cons m t
--   in
--   -- GOAL: all (leq m) t && sorted t
--   trivial
--     `by` minimum_leq xs
--     `by` minimum_permuted xs (Cons m t)
--     `by` sort_permuted xs
--     `by` sort_sorted t

-- {-@
-- assume_permuted :: xs:List -> ys:List -> {permuted xs ys}
-- @-}
-- assume_permuted :: List -> List -> Proof
-- assume_permuted xs ys = trivial

-- {-@
-- sort_permuted :: xs:List -> {permuted xs (sort xs)}
-- @-}
-- sort_permuted :: List -> Proof
-- sort_permuted xs = undefined -- TODO
