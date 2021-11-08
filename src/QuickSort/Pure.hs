module QuickSort.Pure where

import Proof

{-@
type OrdList a = [a]<{\h v -> h <= v}>
@-}
type OrdList a = [a]

{-@
quicksort :: Ord a => xs:[a] -> OrdList a / [len xs, 0]
@-}
quicksort :: Ord a => [a] -> OrdList a
quicksort [] = []
quicksort (x : xs) = partition x xs [] []

{-@
partition :: Ord a =>
  x:a ->
  q:[a] ->
  r:[{v:a | v < x}] ->
  p:[{v:a | x <= v}] ->
  OrdList a / [len p + len r + len q, len q + 1]
@-}
partition :: Ord a => a -> [a] -> [a] -> [a] -> [a]
partition x [] rlt rge = append x (quicksort rlt) (x : quicksort rge)
partition x (y : ys) rlt rge =
  case compare x y of
    GT -> partition x ys (y : rlt) rge
    _ -> partition x ys rlt (y : rge)

-- ! why doesn't this also work??
-- if y <= x
--   then partition x ys (y : rlt) rge
--   else partition x ys rlt (y : rge)

{-@
append ::
  x:a ->
  OrdList ({v:a | v < x}) ->
  OrdList ({v:a | x <= v}) ->
  OrdList a
@-}
append :: Ord a => a -> [a] -> [a] -> [a]
append k [] ys = ys
append k (x : xs) ys = x : append k xs ys
