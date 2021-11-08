{-@ LIQUID "--compile-spec" @-}

module SelectionSort.Pure where

import Proof
import Refined.Data.Int
import Refined.Data.List

-- selection sort

{-@ reflect sort @-}
sort :: List -> List
sort Nil = Nil
sort (Cons x Nil) = Cons x Nil
sort (Cons x xs) =
  let Cons x' xs' = select (Cons x xs)
   in Cons x' (sort xs')

-- sorted_sort

{-@ automatic-instances sorted_sort @-}
{-@
sorted_sort :: xs:List -> Sorted {sort xs}
@-}
sorted_sort :: List -> Sorted
-- i and j cannot be in bounds for Nil
sorted_sort Nil i j = trivial
sorted_sort (Cons x xs) i j =
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
                  (permuted_sort xs')
                  ( index
                      (sort xs')
                      ((j `by` lng_permuted xs' (sort xs') (permuted_sort xs')) - 1)
                  )
              )
        else -- GOAL: index (sort xs') (i - 1) <= index (sort xs') (j - 1)
          sorted_sort xs' (i - 1) (j - 1)

-- permuted_sort

{-@ automatic-instances permuted_sort @-}
{-@ lazy permuted_sort @-}
{-@
permuted_sort :: xs:List -> Permuted {xs} {sort xs}
@-}
permuted_sort :: List -> Permuted
permuted_sort Nil = \z -> trivial
permuted_sort (Cons x xs) =
  let Cons x' xs' = select (Cons x xs)
   in permuted_transitive
        (Cons x xs)
        (Cons x' xs')
        (Cons x' (sort xs'))
        (permuted_select (Cons x xs))
        ( permuted_tl
            (Cons x' xs')
            ( Cons x' (sort xs')
                `by` hd_reduce x' xs'
                `by` hd_reduce x' (sort xs')
            )
            (permuted_sort (xs' `by` lng_permuted (Cons x' xs') (Cons x' (sort xs')) (permuted_sort xs')))
        )

{-@ automatic-instances hd_reduce @-}
{-@
hd_reduce :: x:Int -> xs:List -> {x == hd (Cons x xs)}
@-}
hd_reduce :: Int -> List -> Proof
hd_reduce x Nil = trivial
hd_reduce x (Cons y ys) = trivial
