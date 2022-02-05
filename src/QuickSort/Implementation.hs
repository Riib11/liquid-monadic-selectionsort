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

-- quicksort

quicksort :: Array m -> m Unit
quicksort iA =
  if lengthA iA <= 0
    then pureA iA unit
    else quicksort_go iA 0 (lengthA iA - 1)

{-@
quicksort_go :: iA:Array m -> i:{Ix | inBoundsA iA i} -> j:{Ix | inBoundsA iA j && i <= j} -> m Unit
@-}
quicksort_go :: Array m -> Ix -> Ix -> m Unit
quicksort_go iA i j =
  (bindA iA)
    (partition iA i i i j)
    (quicksort_go_aux iA i j)

{-@
quicksort_go_aux :: iA:Array m -> i:{Ix | inBoundsA iA i} -> j:{Ix | inBoundsA iA j} -> iP:Ix -> m Unit
@-}
quicksort_go_aux :: Array m -> Ix -> Ix -> Ix -> m Unit
quicksort_go_aux iA i j iP =
  (seqA iA)
    ( if 0 <= sub1 iP - i && sub1 iP - i < j - i && inBoundsA iA (sub1 iP)
        then quicksort_go iA i (sub1 iP)
        else pureA iA unit
    )
    ( if 0 <= j - add1 iP && j - add1 iP < j - i && inBoundsA iA (add1 iP)
        then quicksort_go iA (add1 iP) j
        else pureA iA unit
    )

{-@ automatic-instances partition @-}
{-@
partition ::
  iA:Array m ->
  iLf:{Ix | inBoundsA iA iLf} ->
  iLo:{Ix | inBoundsA iA iLo && 0 <= iLo && iLo < lengthA iA && iLf <= iLo} ->
  iHi:{Ix | inBoundsA iA iHi && iLf <= iHi && iHi <= iLo} ->
  iP:{Ix | inBoundsA iA iP && iLo <= iP} ->
  m ({iP':Ix | inBoundsA iA iP' && iLf <= iP' && iP' <= iP})
@-}
partition :: Array m -> Ix -> Ix -> Ix -> Ix -> m Ix
partition iA iLf iLo iHi iP =
  if iLo < iP
    then
      (bindA iA)
        (readA iA iLo)
        (partition_aux1 iA iLf iLo iHi iP)
    else
      (seqA iA)
        (swapA iA iHi iP)
        (pureA iA (iHi `by` assume (inBoundsA iA iHi && iLf <= iHi && iHi <= iP)))

{-@
partition_aux1 ::
  iA:Array m ->
  iLf:{Ix | inBoundsA iA iLf} ->
  iLo:{Ix | inBoundsA iA iLo && iLf <= iLo} ->
  iHi:{Ix | inBoundsA iA iHi && iLf <= iHi && iHi <= iLo} ->
  iP:{Ix | inBoundsA iA iP && iLo <= iP} ->
  lo:El ->
  m ({iP':Ix | inBoundsA iA iP' && iLf <= iP' && iP' <= iP})
@-}
partition_aux1 :: Array m -> Ix -> Ix -> Ix -> Ix -> El -> m Ix
partition_aux1 iA iLf iLo iHi iP lo =
  (bindA iA)
    (readA iA iP)
    (partition_aux2 iA iLf iLo iHi iP lo)

{-@
partition_aux2 ::
  iA:Array m ->
  iLf:Ix ->
  iLo:{Ix | inBoundsA iA iLo && iLf <= iLo} ->
  iHi:{Ix | inBoundsA iA iHi && iLf <= iHi && iHi <= iLo} ->
  iP:{Ix | inBoundsA iA iP && iLo <= iP} ->
  lo:El ->
  p:El ->
  m ({iP':Ix | inBoundsA iA iP' && iLf <= iP' && iP' <= iP})
@-}
partition_aux2 :: Array m -> Ix -> Ix -> Ix -> Ix -> El -> El -> m Ix
partition_aux2 iA iLf iLo iHi iP lo p =
  if lo > p
    then partition iA iLf (add1 iLo) iHi iP
    else
      (seqA iA)
        (swapA iA iLo iHi)
        (partition iA iLf (add1 iLo) (add1 iHi) iP)
