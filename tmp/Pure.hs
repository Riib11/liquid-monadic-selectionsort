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
