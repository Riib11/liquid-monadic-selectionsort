{-@ LIQUID "--compile-spec" @-}
module Refined.Data.List where

import Proof
import Prelude hiding (all, any, length, min, minimum)

{-@ reflect le @-}
le :: Int -> Int -> Bool
le x y = x <= y

{-@ reflect eq @-}
eq :: Int -> Int -> Bool
eq x y = x == y

-- data List

data List = Nil | Cons Int List
  deriving (Show, Eq)

infixr 5 `Cons`

-- List uses length as a termination measure
{-@ data List [length] @-}

-- length

{-@ measure length @-}
{-@
length :: List -> {l:Int | 0 <= l}
@-}
length :: List -> Int
length Nil = 0
length (Cons x xs) = 1 + length xs

-- hd (head)

{-@ reflect hd @-}
{-@
hd :: {xs:List | 0 < length xs} -> {x:Int | contains xs x}
@-}
hd :: List -> Int
hd (Cons x xs) = x

-- tl (tail)

{-@ reflect tl @-}
{-@
tl :: {xs:List | 0 < length xs} -> {xs':List | length xs = length xs' + 1}
@-}
tl :: List -> List
tl (Cons x xs) = xs

-- contains_cons

-- TODO
{-@
contains_cons ::
  {xs:List | 0 < length xs} ->
  {y:Int | contains xs y} ->
  {y == hd xs || contains (tl xs) y}
@-}
contains_cons :: List -> Int -> Proof
contains_cons xs y = undefined

-- index

{-@ automatic-instances index @-}
{-@ reflect index @-}
{-@
index :: xs:List -> {i:Int | inBounds xs i} -> {x:Int | contains xs x}
@-}
index :: List -> Int -> Int
index (Cons x xs) i = if i <= 0 then x else index xs (i - 1)

-- The index `i` is in bounds of `xs`
{-@ inline inBounds @-}
inBounds :: List -> Int -> Bool
inBounds xs i = 0 <= i && i < length xs

-- contains

{-@ reflect contains @-}
contains :: List -> Int -> Bool
-- contains xs y = any (eq y) xs
contains xs y = 0 < count xs y

-- index_0_hd

{-@ automatic-instances index_0_hd @-}
{-@
index_0_hd :: {xs:List | 0 < length xs} -> {index xs 0 = hd xs}
@-}
index_0_hd :: List -> Int -> Proof
index_0_hd xs i = trivial

-- `count xs y` computes the number of times that `y` appears in `xs`.
{-@ reflect count @-}
count :: List -> Int -> Int
count Nil _ = 0
count (Cons x xs) y = if x == y then 1 + count xs y else count xs y

-- LeAll

{-@
type LeAll X XS = y:Int -> {contains XS y => X <= y}
@-}
type LeAll = Int -> Proof

-- minimumIndex

{-@ automatic-instances minimumIndex @-}
{-@ reflect minimumIndex @-}
{-@
minimumIndex :: {xs:List | length xs > 0} -> {i:Int | inBounds xs i}
@-}
minimumIndex :: List -> Int
minimumIndex (Cons x Nil) = 0
minimumIndex (Cons x (Cons x' xs)) = if x <= x' then 0 else 1 + minimumIndex (Cons x' xs)

-- swap

-- {-@ reflect swap @-}
-- {-@
-- swap ::
--   {i:Int | inBounds xs i} -> {i:Int | inBounds xs j} ->
--   {xs:List | 2 < length xs} ->
--   List
-- @-}
-- swap :: Int -> Int -> List -> List
-- swap i j (Cons x (Cons x' Nil)) =

-- select

{-@ reflect select @-}
{-@
select :: {xs:List | 0 < length xs} -> {xs':List | length xs == length xs'}
@-}
select :: List -> List
select (Cons x Nil) = Cons x Nil
select (Cons x1 (Cons x2 xs)) =
  if x1 <= x2
    then
      let (Cons x' xs') = select (Cons x1 xs)
       in Cons x' (Cons x2 xs')
    else
      let (Cons x' xs') = select (Cons x2 xs)
       in Cons x' (Cons x1 xs')

-- select_leAll

-- ! PROTO

-- select_permuted

-- swap_front_permuted

{-@ automatic-instances swap_front_permuted @-}
{-@
swap_front_permuted ::
  x1:Int -> x2:Int -> xs:List ->
  Permuted {Cons x1 (Cons x2 xs)} {Cons x2 (Cons x1 xs)}
@-}
swap_front_permuted :: Int -> Int -> List -> Permuted
swap_front_permuted x1 x2 xs y =
  if y == x1
    then if y == x2 then trivial else trivial
    else if y == x2 then trivial else trivial

-- select_permuted

{-@ automatic-instances select_permuted @-}
{-@
select_permuted ::
  {xs:List | 0 < length xs} ->
  Permuted {xs} {select xs}
@-}
select_permuted :: List -> Permuted
-- must have x = y
select_permuted (Cons x Nil) y = trivial
select_permuted (Cons x1 (Cons x2 xs)) y =
  if x1 <= x2
    then
      let (Cons x' xs') = select (Cons x1 xs)
          xs1 = Cons x1 (Cons x2 xs)
          p12 = swap_front_permuted x1 x2 xs
          xs2 = Cons x2 (Cons x1 xs)
          p23 = select_permuted (Cons x1 xs)
          xs3 = Cons x2 (Cons x' xs')
          p34 = swap_front_permuted x2 x' xs'
          xs4 = Cons x' (Cons x2 xs')
       in (permuted_transitive xs1 xs2 xs4 p12)
            (permuted_transitive xs2 xs3 xs4 p23 p34)
            y
    else
      let (Cons x' xs') = select (Cons x2 xs)
          xs1 = Cons x1 (Cons x2 xs)
          p12 = select_permuted (Cons x2 xs)
          xs2 = Cons x1 (Cons x' xs')
          p23 = swap_front_permuted x1 x' xs'
          xs3 = Cons x' (Cons x1 xs')
       in permuted_transitive xs1 xs2 xs3 p12 p23 y

-- sorted

{-@
type Sorted XS = {i:Int | inBounds xs i} -> {j:Int | inBounds xs j && i <= j} -> {index XS i <= index XS j}
@-}
type Sorted = Int -> Int -> Proof

-- type Permuted

{-@
type Permuted XS YS = z:Int -> {permutedAt XS YS z}
@-}
type Permuted = Int -> Proof

{-@ reflect permutedAt @-}
permutedAt :: List -> List -> Int -> Bool
permutedAt xs ys z = count xs z == count ys z

-- permuted_reflexive

{-@ automatic-instances permuted_reflexive @-}
{-@
permuted_reflexive :: xs:List -> Permuted {xs} {xs}
@-}
permuted_reflexive :: List -> Permuted
permuted_reflexive xs = \x -> trivial

-- permuted_symmetric

{-@ automatic-instances permuted_symmetric @-}
{-@
permuted_symmetric ::
  xs:List -> ys:List ->
  Permuted {xs} {ys} ->
  Permuted {ys} {xs}
@-}
permuted_symmetric :: List -> List -> Permuted -> Permuted
permuted_symmetric xs ys p y = p y

-- permuted_transitive

{-@ automatic-instances permuted_transitive @-}
{-@
permuted_transitive ::
  xs:List -> ys:List -> zs:List ->
  Permuted {xs} {ys} ->
  Permuted {ys} {zs} ->
  Permuted {xs} {zs}
@-}
permuted_transitive :: List -> List -> List -> Permuted -> Permuted -> Permuted
permuted_transitive xs ys zs pxy pyz y = trivial `by` pyz y `by` pxy y

-- permuted_contains

{-@ automatic-instances permuted_contains @-}
{-@
permuted_contains ::
  xs:List ->
  ys:List ->
  Permuted {xs} {ys} ->
  {z:Int | contains xs z} ->
  {contains ys z}
@-}
permuted_contains :: List -> List -> Permuted -> Int -> Proof
permuted_contains xs ys p z = p z

-- leAll_permuted

{-@ reflect leAll_permuted @-}
{-@ automatic-instances leAll_permuted @-}
{-@
leAll_permuted ::
  x:Int ->
  xs:List ->
  LeAll {x} {xs} ->
  ys:List ->
  Permuted {xs} {ys} ->
  LeAll {x} {ys}
@-}
leAll_permuted :: Int -> List -> LeAll -> List -> Permuted -> LeAll
-- leAll: y:Int -> {contains xs y => x <= y}
-- {y:Int | contains ys y}
-- GOAL: x <= y
leAll_permuted x xs leAll ys perm y = leAll (y `by` perm y)
