{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--short-names" @-}

module QuickSort.Implementation where

import Proof
import QuickSort.Array
import Refined.Data.Int
import Refined.Data.Unit
import Refined.Function
import Relation.Equality.Leibniz

-- -- quicksort

-- quicksort :: Array m -> m Unit
-- quicksort _A =
--   if lengthArray _A <= 0
--     then pureArray _A unit
--     else quicksort_go _A 0 (lengthArray _A - 1)

-- {-@
-- quicksort_go :: _A:Array m -> i:Ix {_A} -> {j:Ix {_A} | i <= j} -> m Unit
-- @-}
-- quicksort_go :: Array m -> Ix -> Ix -> m Unit
-- quicksort_go _A i j =
--   (bindArray _A)
--     (partition _A i i i j)
--     (quicksort_go_aux _A i j)

-- {-@
-- quicksort_go_aux :: _A:Array m -> i:Ix {_A} -> j:Ix {_A} -> iP:Ix {_A} -> m Unit
-- @-}
-- quicksort_go_aux :: Array m -> Ix -> Ix -> Ix -> m Unit
-- quicksort_go_aux _A i j iP =
--   (seqArray _A)
--     ( if 0 <= sub1 iP - i && sub1 iP - i < j - i && inBoundsArray _A (sub1 iP)
--         then quicksort_go _A i (sub1 iP)
--         else pureArray _A unit
--     )
--     ( if 0 <= j - add1 iP && j - add1 iP < j - i && inBoundsArray _A (add1 iP)
--         then quicksort_go _A (add1 iP) j
--         else pureArray _A unit
--     )

-- {-@ automatic-instances partition @-}
-- {-@
-- assume partition ::
--   _A:Array m ->
--   iLf:Ix {_A} ->
--   iLo:{Int | 0 <= iLo && iLo < lengthArray _A && iLf <= iLo} ->
--   iHi:{Ix {A_} | iLf <= iHi && iHi <= iLo} ->
--   iP:{Ix {_A} | iLo <= iP} ->
--   m ({iP':Ix {_A} | iLf <= iP' && iP' <= iP})
-- @-}
-- partition :: Array m -> Ix -> Ix -> Ix -> Ix -> m Ix
-- partition _A iLf iLo iHi iP =
--   if iLo < iP
--     then
--       (bindArray _A)
--         (readArray _A iLo)
--         (partition_aux1 _A iLf iLo iHi iP)
--     else
--       (seqArray _A)
--         (swapArray _A iHi iP)
--         (pureArray _A iHi)
--         `by` undefined

-- {-@
-- partition_aux1 ::
--   _A:Array m ->
--   iLf:Ix {_A} ->
--   iLo:{iLo:Ix {_A} | iLf <= iLo} ->
--   iHi:{iHi:Ix {A_} | iLf <= iHi && iHi <= iLo} ->
--   iP:{iP:Ix {_A} | iLo <= iP} ->
--   lo:El ->
--   m ({iP':Ix {_A} | iLf <= iP' && iP' <= iP})
-- @-}
-- partition_aux1 :: Array m -> Ix -> Ix -> Ix -> Ix -> El -> m Ix
-- partition_aux1 _A iLf iLo iHi iP lo =
--   (bindArray _A)
--     (readArray _A iP)
--     (partition_aux2 _A iLf iLo iHi iP lo)

-- {-@
-- partition_aux2 ::
--   _A:Array m ->
--   iLf:Ix {_A} ->
--   iLo:{iLo:Ix {_A} | iLf <= iLo} ->
--   iHi:{iHi:Ix {A_} | iLf <= iHi && iHi <= iLo} ->
--   iP:{iP:Ix {_A} | iLo <= iP} ->
--   lo:El ->
--   p:El ->
--   m ({iP':Ix {_A} | iLf <= iP' && iP' <= iP})
-- @-}
-- partition_aux2 :: Array m -> Ix -> Ix -> Ix -> Ix -> El -> El -> m Ix
-- partition_aux2 _A iLf iLo iHi iP lo p =
--   if lo > p
--     then partition _A iLf (add1 iLo) iHi iP
--     else
--       (seqArray _A)
--         (swapArray _A iLo iHi)
--         (partition _A iLf (add1 iLo) (add1 iHi) iP)