# liquid-monadic-selectionsort

## Pure Selection Sort

### Sorting

```haskell
{-@
sort :: List -> List
@-}
sort :: List -> List
sort Nil = Nil
sort (Cons x Nil) = Cons x Nil
sort (Cons x xs) =
  let Cons x' xs' = select (Cons x xs)
   in Cons x' (sort xs')
```

### Correctness Specifications

```haskell
{-@
sorted_sort :: xs:List -> Sorted {sort xs}
@-}
sorted_sort :: List -> Sorted

{-@
permuted_sort :: xs:List -> Permuted {xs} {sort xs}
@-}
permuted_sort :: List -> Permuted
```

### Proofs of Correctness

See module `SelectionSort/Pure.hs`.

### Predicates

```haskell
-- the list XS is sorted
{-@
type Sorted XS = {i:Int | inBounds xs i} -> {j:Int | inBounds xs j && i <= j} -> {index XS i <= index XS j}
@-}
type Sorted = Int -> Int -> Proof

-- the list XS is a permutation of the list YS
{-@
type Permuted XS YS = z:Int -> {permutedAt XS YS z}
@-}
type Permuted = Int -> Proof

permutedAt :: List -> List -> Int -> Bool
permutedAt xs ys z = count xs z == count ys z

-- the int X is less than or equal to each element of XS
{-@
type LeAll X XS = y:Int -> {contains XS y => X <= y}
@-}
type LeAll = Int -> Proof
```

### Performance

```
stack build  69.37s user 8.18s system 93% cpu 1:22.88 total
```

## Stateful Selection Sort

TODO
