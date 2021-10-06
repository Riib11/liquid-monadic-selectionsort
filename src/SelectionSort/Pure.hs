module SelectionSort.Pure where

import Proof
import Refined.Data.List
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

-- TODO
{-@ automatic-instances sort_sorted @-}
{-@
sort_sorted :: xs:List -> {sorted (sort xs)}
@-}
sort_sorted :: List -> Proof
sort_sorted Nil = undefined -- trivial
sort_sorted (Cons x Nil) = undefined -- trivial
{-
SUBGOAL#1: leAll (hd xs') (sort (tl xs'))
PROOF.
  leAll (hd xs') (tl xs')
    by pf1 := select_leAll (Cons x xs)
  permuted (tl xs') (sort (tl xs'))
    by pf2 := sort_permuted (tl xs')
  leAll (hd xs') (sort (tl xs'))
    by permuted_leAll
        (hd xs')
        (tl xs' `by` pf1)
        (sort (tl xs') `by` pf2)
END.

SUBGOAL#2: sorted (sort (tl xs'))
PROOF.
  trivial by sort_sorted (tl xs')
END.
-}
sort_sorted (Cons x xs) =
  let Cons x' xs' = select (Cons x xs)
   in trivial
        -- SUBGOAL#1
        `by` ( permuted_leAll
                 x'
                 (xs' `by` select_leAll (Cons x xs))
                 (sort xs' `by` sort_permuted xs')
             )
        -- SUBGOAL#2
        `by` sort_sorted xs'

-- sort_permuted

-- TODO
{-@
assume sort_permuted :: xs:List -> {permuted xs (sort xs)}
@-}
sort_permuted :: List -> Proof
sort_permuted xs = undefined
