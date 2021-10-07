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
-- contains xs y = any (eq y) xs
contains xs y = 0 < count xs y

-- all

{-@ reflect all @-}
all :: (Int -> Bool) -> List -> Bool
all p Nil = True
all p (Cons x xs) = p x && all p xs

-- all_contains

{-@
all_contains ::
  p:(Int -> Bool) ->
  {xs:List | all p xs} ->
  {x:Int | contains xs x} ->
  {p x}
@-}
all_contains :: (Int -> Bool) -> List -> Int -> Proof
all_contains p xs x = undefined

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

-- LeAll

{-@
type LeAll X XS = y:Int -> {contains xs y => x <= y}
@-}
type LeAll = Int -> Proof

-- leAll

-- ! OLD
-- {-@ reflect leAll @-}
-- leAll :: Int -> List -> Bool
-- leAll x xs = all (le x) xs

-- leAll_contains_le

{-@
leAll_contains_le ::
  x:Int ->
  {xs:List | leAll x xs} ->
  {x':Int | contains xs x'} ->
  {x <= x'}
@-}
leAll_contains_le :: Int -> List -> Int -> Proof
leAll_contains_le x xs y = undefined

{-@
leAll_contains ::
  x:Int ->
  ys:List ->
  (y:Int -> {contains ys y => x <= y}) ->
  {leAll x ys}
@-}
leAll_contains :: Int -> List -> Permuted -> Proof
leAll_contains xx ys h = undefined

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

-- type Permuted

{-@
type Permuted XS YS = z:Int -> {permutedAt XS YS z}
@-}
type Permuted = Int -> Proof

-- ! OLD
-- {-@ reflect permuted @-}
-- {-@
-- permuted :: List -> List -> Bool
-- @-}
-- permuted :: List -> List -> Bool
-- permuted xs ys = all (permutedAt xs ys) xs && all (permutedAt xs ys) ys

{-@ reflect permutedAt @-}
permutedAt :: List -> List -> Int -> Bool
permutedAt xs ys z = count xs z == count ys z

-- `count xs y` computes the number of times that `y` appears in `xs`.
{-@ reflect count @-}
count :: List -> Int -> Int
count Nil _ = 0
count (Cons x xs) y = if x == y then 1 + count xs y else count xs y

-- permuted_reflexive

{-@ automatic-instances permuted_reflexive @-}
{-@
permuted_reflexive :: xs:List -> Permuted {xs} {xs}
@-}
permuted_reflexive :: List -> Permuted
permuted_reflexive xs = \x -> trivial

-- permuted_symmetric

{-@
permuted_symmetric ::
  xs:List -> ys:List ->
  Permuted {xs} {ys} ->
  Permuted {ys} {xs}
@-}
permuted_symmetric :: List -> List -> Permuted -> Permuted
permuted_symmetric xs ys p = undefined

-- TODO: disabled cuz of new def of contains to be in terms of count
-- -- count_contains

-- {-@
-- count_contains :: xs:List -> {x:Int | contains xs x} -> {contains xs x}
-- @-}
-- count_contains :: List -> Int -> Proof
-- count_contains xs x = undefined

-- -- count_contains

-- {-@ automatic-instances contains_count @-}
-- {-@
-- contains_count :: xs:List -> {x:Int | contains xs x} -> {0 < count xs x}
-- @-}
-- contains_count :: List -> Int -> Proof
-- contains_count Nil x = trivial
-- -- y: contains (Cons xs x) y
-- contains_count (Cons x xs) y = undefined

-- TODO
---- not_permuted_Nil_Cons, not_permuted_Cons_Nil

-- {-@
-- not_permuted_Nil_Cons ::
--   x:Int -> xs:List ->
--   {not (permuted Nil (Cons x xs))}
-- @-}
-- not_permuted_Nil_Cons :: Int -> List -> Proof
-- not_permuted_Nil_Cons x xs = undefined

-- {-@
-- not_permuted_Cons_Nil ::
--   x:Int -> xs:List ->
--   {not (permuted (Cons x xs) Nil)}
-- @-}
-- not_permuted_Cons_Nil :: Int -> List -> Proof
-- not_permuted_Cons_Nil x xs = undefined

-- TODO
-- -- permuted_length

-- {-@ automatic-instances permuted_length @-}
-- {-@
-- permuted_length ::
--   xs:List -> {ys:List | permuted xs ys} ->
--   {length xs == length ys}
-- @-}
-- permuted_length :: List -> List -> Proof
-- permuted_length Nil Nil = trivial
-- {-
-- permuted Nil (Cons y ys)
-- =
-- all (eqCounts Nil (Cons y ys)) Nil &&
-- all (eqCounts Nil (Cons y ys)) (Cons y ys)
-- =
-- all (eqCounts Nil (Cons y ys)) (Cons y ys)
-- =
-- count Nil y == count (Cons y ys) y &&
-- all (eqCounts Nil (Cons y ys)) ys
-- =
-- 0 = 1 &&
-- all (eqCounts Nil (Cons y ys)) ys
-- -}
-- permuted_length Nil (Cons y ys) = not_permuted_Nil_Cons y ys
-- permuted_length (Cons x xs) Nil = not_permuted_Cons_Nil x xs
-- permuted_length (Cons x xs) (Cons y ys) = undefined

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

-- permuted_not_contains

-- permuted_not_contains :: List -> List
-- leAll_permuted_leAll

-- {-@ reflect leAll_permuted_leAll @-}
{-@ automatic-instances leAll_permuted_leAll @-}
{-@
leAll_permuted_leAll ::
  x:Int ->
  {xs:List | leAll x xs} ->
  ys:List ->
  Permuted {xs} {ys} ->
  {leAll x ys}
@-}
leAll_permuted_leAll :: Int -> List -> List -> Permuted -> Proof
-- xs: leAll x xs
-- p: Permuted xs ys
-- goal1: leAll x ys
leAll_permuted_leAll x xs ys p =
  leAll_contains
    x
    ys
    ( \y ->
        -- y: contains ys y
        -- lem1: contains xs y // permuted_contains xs ys p y
        -- G2: x <= y // by leAll_contains_le x xs (y `by` lem1)
        if contains ys y
          then
            (leAll_contains_le x xs)
              (y `by` permuted_contains ys xs (permuted_symmetric xs ys p) y)
          else trivial
    )
