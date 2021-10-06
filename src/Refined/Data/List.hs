-- {-@ LIQUID "--compile-spec" @-}
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
hd :: {xs:List | 0 < length xs} -> Int
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

-- index

{-@ automatic-instances index @-}
{-@ reflect index @-}
{-@
index :: xs:List -> {i:Int | inBounds xs i} -> Int
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
contains xs y = any (eq y) xs

-- all

{-@ reflect all @-}
all :: (Int -> Bool) -> List -> Bool
all p Nil = True
all p (Cons x xs) = p x && all p xs

-- any

{-@ reflect any @-}
any :: (Int -> Bool) -> List -> Bool
any p Nil = False
any p (Cons x xs) = p x || any p xs

-- exists

{-@ reflect exists @-}
exists :: (Int -> Bool) -> List -> Bool
exists p Nil = False
exists p (Cons x xs) = p x || exists p xs

-- leAll

{-@ reflect leAll @-}
leAll :: Int -> List -> Bool
leAll x xs = all (le x) xs

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
       in Cons x' (Cons x2 xs')

-- -- {-@ reflect select_length @-}
-- {-@ automatic-instances select_length @-}
-- {-@
-- select_length ::
--   {xs:List | 0 < length xs} ->
--   {length xs == length (select xs)}
-- @-}
-- select_length :: List -> Proof
-- select_length (Cons x Nil) = trivial
-- -- GOAL: length (Cons x1 (Cons x2 xs)) == length (select (Cons x1 (Cons x2 xs)))
-- select_length (Cons x1 (Cons x2 xs')) =
--   if x1 <= x2
--     then
--       select_length (Cons x1 xs')
--         `by` assume_eq (length (select (Cons x1 xs'))) (length (tl (select (Cons x1 xs'))))
--     else -- `by` tl (select (Cons x1 xs') `by` select_length (Cons x1 xs'))

--       select_length (Cons x2 xs')
--         `by` tl (select (Cons x2 xs') `by` select_length (Cons x2 xs'))

{-@
select_leAll ::
  {xs:List | 0 < length xs} ->
  {leAll (hd (select xs)) (tl (select xs))}
@-}
select_leAll :: List -> Proof
select_leAll xs = undefined

-- sorted

{-@ reflect sorted @-}
sorted :: List -> Bool
sorted Nil = True
sorted (Cons x xs) = leAll x xs && sorted xs

{-@
assume
assume_sorted :: xs:List -> {sorted xs}
@-}
assume_sorted :: List -> Proof
assume_sorted xs = trivial

-- permuted

-- {-@ reflect permuted @-}
-- permuted :: List -> List -> Bool
-- permuted xs ys = all (contains ys) xs -- ! won't work because ignores duplicates

{-@ reflect permuted @-}
{-@
permuted :: List -> List -> Bool
@-}
permuted :: List -> List -> Bool
permuted xs ys = all (eqCounts xs ys) xs && all (eqCounts xs ys) ys

{-@ reflect eqCounts @-}
{-@
eqCounts :: List -> List -> Int -> Bool
@-}
eqCounts :: List -> List -> Int -> Bool
eqCounts xs ys z = count xs z == count ys z

{-@
assume
assume_permuted :: xs:List -> ys:List -> {permuted xs ys}
@-}
assume_permuted :: List -> List -> Proof
assume_permuted xs ys = trivial

-- `count xs y` computes the number of times that `y` appears in `xs`.
{-@ reflect count @-}
count :: List -> Int -> Int
count Nil _ = 0
count (Cons x xs) y = if x == y then 1 + count xs y else count xs y

-- not_permuted_Nil_Cons, not_permuted_Cons_Nil

{-@
not_permuted_Nil_Cons ::
  x:Int -> xs:List ->
  {not (permuted Nil (Cons x xs))}
@-}
not_permuted_Nil_Cons :: Int -> List -> Proof
not_permuted_Nil_Cons x xs = undefined

{-@
not_permuted_Cons_Nil ::
  x:Int -> xs:List ->
  {not (permuted (Cons x xs) Nil)}
@-}
not_permuted_Cons_Nil :: Int -> List -> Proof
not_permuted_Cons_Nil x xs = undefined

-- permuted_length

{-@ automatic-instances permuted_length @-}
{-@
permuted_length ::
  xs:List -> {ys:List | permuted xs ys} ->
  {length xs == length ys}
@-}
permuted_length :: List -> List -> Proof
permuted_length Nil Nil = trivial
{-
permuted Nil (Cons y ys)
=
all (eqCounts Nil (Cons y ys)) Nil &&
all (eqCounts Nil (Cons y ys)) (Cons y ys)
=
all (eqCounts Nil (Cons y ys)) (Cons y ys)
=
count Nil y == count (Cons y ys) y &&
all (eqCounts Nil (Cons y ys)) ys
=
0 = 1 &&
all (eqCounts Nil (Cons y ys)) ys
-}
permuted_length Nil (Cons y ys) = not_permuted_Nil_Cons y ys
permuted_length (Cons x xs) Nil = not_permuted_Cons_Nil x xs
permuted_length (Cons x xs) (Cons y ys) = undefined

-- permuted_leAll

-- {-@ reflect permuted_leAll @-}
{-@
permuted_leAll ::
  x:Int ->
  {xs:List | leAll x xs} ->
  {ys:List | permuted xs ys} ->
  {leAll x ys}
@-}
permuted_leAll :: Int -> List -> List -> Proof
permuted_leAll x xs ys = undefined -- TODO
