module SelectionSort.Pure where

import Proof
import Refined.Data.List
import Refined.Data.ListProto
import Prelude hiding (all, any, length, min, minimum)

-- sort

{-@ reflect sort @-}
{-@
sort :: List -> List
@-}
sort :: List -> List
sort Nil = Nil
sort (Cons x Nil) = Cons x Nil
sort (Cons x xs) =
  let Cons x' xs' = select (Cons x xs)
   in Cons x' (sort xs')

-- sort_sorted

{-@ automatic-instances sort_sorted @-}
{-@
sort_sorted :: xs:List -> Sorted {sort xs}
@-}
sort_sorted :: List -> Sorted
-- i and j cannot be in bounds for Nil
sort_sorted Nil i j = trivial
-- i: Int | inBounds (sort (Cons x xs)) i
-- j: Int | inBounds (sort (Cons x xs)) i
sort_sorted (Cons x xs) i j =
  let Cons x' xs' = select (Cons x xs)
   in -- GOAL: index (Cons x' (sort xs')) j <= index (Cons x' (sort xs')) j
      if i <= 0
        then -- GOAL: x' <= index (Cons x' (sort xs')) j 0

          if j <= 0
            then -- GOAL: x' <= x'
              trivial
            else -- GOAL: x' <= index (sort xs') (j - 1)

              ( leAll_permuted
                  x'
                  xs'
                  (select_leAll (Cons x xs))
                  (sort xs')
                  (sort_permuted xs')
                  (index (sort xs') ((j `by` permuted_length xs' (sort xs') (sort_permuted xs')) - 1))
              )
        else -- GOAL: index (sort xs') (i - 1) <= index (sort xs') (j - 1)
          sort_sorted xs' (i - 1) (j - 1)

-- sort_permuted

-- TODO
{-@
assume sort_permuted :: xs:List -> Permuted {xs} {sort xs}
@-}
sort_permuted :: List -> Permuted
sort_permuted xs = undefined
