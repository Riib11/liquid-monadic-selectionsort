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

{-@ automatic-instances contains_cons @-}
{-@ reflect contains_cons @-}
{-@
contains_cons ::
  {xs:List | 0 < length xs} ->
  {y:Int | contains xs y} ->
  {y == hd xs || contains (tl xs) y}
@-}
contains_cons :: List -> Int -> Proof
contains_cons (Cons x xs) y =
  if x == y
    then trivial
    else trivial

-- contains_tl

{-@
contains_tl ::
  {xs:List | 0 < length xs} ->
  {y:Int | contains xs y && y /= hd xs} ->
  {contains (tl xs) y}
@-}
contains_tl :: List -> Int -> Proof
contains_tl xs y = contains_cons xs y

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

-- count_le_0

{-@ automatic-instances count_le_0 @-}
{-@
count_le_0 :: xs:List -> y:Int -> {0 <= count xs y}
@-}
count_le_0 :: List -> Int -> Proof
count_le_0 Nil y = trivial
count_le_0 (Cons x xs) y =
  if x == y
    then count_le_0 xs y
    else count_le_0 xs y

-- count_hd

{-@ automatic-instances count_hd @-}
{-@
count_hd :: {xs:List | 0 < length xs} -> {0 < count xs (hd xs)}
@-}
count_hd :: List -> Proof
count_hd (Cons x Nil) = trivial
count_hd (Cons x xs) = count_le_0 xs x

-- contains_hd

{-@ automatic-instances contains_hd @-}
{-@
contains_hd ::
  {xs:List | 0 < length xs} ->
  {contains xs (hd xs)}
@-}
contains_hd :: List -> Proof
contains_hd xs = count_hd xs

-- count_tl

{-@ automatic-instances count_tl @-}
{-@
count_tl ::
  {xs:List | 0 < length xs} ->
  {y:Int | y /= hd xs} ->
  {count xs y == count (tl xs) y}
@-}
count_tl :: List -> Int -> Proof
count_tl (Cons x xs) y = trivial

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

-- remove

{-@ reflect remove @-}
remove :: List -> Int -> List
remove Nil _ = Nil
remove (Cons x xs) y = if x == y then xs else remove xs y

-- remove_contains_count

{-@ automatic-instances remove_contains_count @-}
{-@
remove_contains_count ::
  {xs:List | 0 < length xs} ->
  {y:Int | contains xs y} ->
  {count (remove xs y) y == count xs y - 1}
@-}
remove_contains_count :: List -> Int -> Proof
remove_contains_count (Cons x Nil) y = if x == y then trivial else trivial
remove_contains_count (Cons x xs) y =
  if x == y
    then trivial
    else remove_contains_count xs y

-- remove_contains_count_neq

{-@ automatic-instances remove_contains_count_neq @-}
{-@
remove_contains_count_neq ::
  {xs:List | 0 < length xs} ->
  {y:Int | contains xs y} ->
  {z:Int | z /= y} ->
  {count (remove xs y) z == count xs z}
@-}
remove_contains_count_neq :: List -> Int -> Int -> Proof
remove_contains_count_neq (Cons x Nil) y z = if y == x then trivial else trivial
remove_contains_count_neq (Cons x xs) y z =
  -- GOAL: count (remove (Cons x xs) y) z == count (Cons x xs) z
  if x == y
    then -- GOAL: count xs z == count (Cons x xs) z
      trivial
    else -- GOAL: count (Cons x (remove xs y)) z == count (Cons x xs) z

      if x == z
        then -- GOAL:  1 + count (remove xs y) z == 1 + count xs y
          remove_contains_count_neq xs y z
        else -- GOAL: count (remove xs y) z == count xs z
          remove_contains_count_neq xs y z

-- surface
-- permutes an element from inside a list to the head

{-@ reflect surface @-}
{-@
surface ::
  {xs:List | 0 < length xs} ->
  {y:Int | contains xs y} ->
  {xs':List | length xs == length xs'}
@-}
surface :: List -> Int -> List
surface xs y = Cons y (remove xs y)

-- permuted_surface
-- `surface` is a permutation
{-@ automatic-instances permuted_surface @-}
{-@
permuted_surface ::
  {xs:List | 0 < length xs} ->
  {y:Int | contains xs y} ->
  Permuted {xs} {surface xs y}
@-}
permuted_surface :: List -> Int -> Permuted
permuted_surface xs y z =
  if z == y
    then remove_contains_count xs y
    else -- GOAL: count xs z == count (Cons y (remove xs y)) z

      trivial
        `by` count_tl (Cons y (remove xs y)) z
        `by` remove_contains_count_neq xs y z

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

-- permuted_select

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

-- permuted_select

{-@ automatic-instances permuted_select @-}
{-@
permuted_select ::
  {xs:List | 0 < length xs} ->
  Permuted {xs} {select xs}
@-}
permuted_select :: List -> Permuted
-- must have x = y
permuted_select (Cons x Nil) y = trivial
permuted_select (Cons x1 (Cons x2 xs)) y =
  if x1 <= x2
    then
      let (Cons x' xs') = select (Cons x1 xs)
          xs1 = Cons x1 (Cons x2 xs)
          p12 = swap_front_permuted x1 x2 xs
          xs2 = Cons x2 (Cons x1 xs)
          p23 = permuted_select (Cons x1 xs)
          xs3 = Cons x2 (Cons x' xs')
          p34 = swap_front_permuted x2 x' xs'
          xs4 = Cons x' (Cons x2 xs')
       in (permuted_transitive xs1 xs2 xs4 p12)
            (permuted_transitive xs2 xs3 xs4 p23 p34)
            y
    else
      let (Cons x' xs') = select (Cons x2 xs)
          xs1 = Cons x1 (Cons x2 xs)
          p12 = permuted_select (Cons x2 xs)
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

-- contains_permuted

{-@ automatic-instances contains_permuted @-}
{-@
contains_permuted ::
  xs:List ->
  ys:List ->
  Permuted {xs} {ys} ->
  {z:Int | contains xs z} ->
  {contains ys z}
@-}
contains_permuted :: List -> List -> Permuted -> Int -> Proof
contains_permuted xs ys p z = p z

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

-- permuted_cons

{-@ automatic-instances permuted_cons @-}
{-@
permuted_cons ::
  {xs:List | 0 < length xs} ->
  {ys:List | 0 < length ys && hd xs == hd ys}->
  Permuted {tl xs} {tl ys} ->
  Permuted {xs} {ys}
@-}
permuted_cons :: List -> List -> Permuted -> Permuted
permuted_cons xs ys p z = if z == hd xs then p z else p z

-- permuted_tl

{-@ automatic-instances permuted_tl @-}
{-@
permuted_tl ::
  {xs:List | 0 < length xs} ->
  {ys:List | 0 < length ys && hd xs == hd ys} ->
  Permuted {xs} {ys} ->
  Permuted {tl xs} {tl ys}
@-}
permuted_tl :: List -> List -> Permuted -> Permuted
permuted_tl (Cons x1 Nil) (Cons y1 Nil) p = \z -> trivial
permuted_tl (Cons x1 (Cons x2 xs)) (Cons y1 Nil) p = \z -> trivial `by` p z
permuted_tl (Cons x1 Nil) (Cons y1 (Cons y2 ys)) p = \z -> trivial `by` p z
permuted_tl (Cons x1 (Cons x2 xs)) (Cons y1 (Cons y2 ys)) p = \z -> if z == x1 then p z else p z

-- -- permuted_remove

-- {-@ automatic-instances permuted_remove @-}
-- {-@
-- permuted_remove ::
--   {xs:List | 0 < length xs} ->
--   {ys:List | 0 < length ys} ->
--   {z:Int | contains xs z} ->
--   Permuted {xs} {ys} ->
--   Permuted {tl (surface xs z)} {tl (surface ys z)}
-- @-}
-- permuted_remove :: List -> List -> Int -> Permuted -> Permuted
-- permuted_remove xs ys z p =
--   let z' = z `by` assume_true (contains ys z)
--    in permuted_tl
--         (surface xs z)
--         (surface ys z')
--         ( (permuted_transitive (surface xs z) xs (surface ys z))
--             (permuted_symmetric xs (surface xs z) (permuted_surface xs z))
--             ((permuted_transitive xs ys (surface ys z')) p (permuted_surface ys z'))
--         )
--         `by` undefined -- TODO

-- length_permuted

{-@ automatic-instances length_permuted @-}
{-@
length_permuted ::
  xs:List ->
  ys:List ->
  Permuted {xs} {ys} ->
  {length xs == length ys}
@-}
length_permuted :: List -> List -> Permuted -> Proof
length_permuted Nil Nil p = trivial
length_permuted Nil (Cons y ys) p = trivial `by` p y `by` count_hd (Cons y ys)
length_permuted (Cons x xs) Nil p = trivial `by` p x `by` count_hd (Cons x xs)
length_permuted (Cons x xs) (Cons y ys) p =
  let x' = x `by` contains_permuted (Cons x xs) (Cons y ys) p (x `by` contains_hd (Cons x xs))
   in trivial
        `by` length_permuted
          xs
          (tl (surface (Cons y ys) x'))
          ( permuted_tl
              (Cons x xs)
              (surface (Cons y ys) x')
              ( (permuted_transitive (Cons x xs) (Cons y ys) (surface (Cons y ys) x'))
                  p
                  (permuted_surface (Cons y ys) (x `by` p x))
              )
          )
        `by` assume_eq (length (Cons y ys)) (length (surface (Cons y ys) x'))

-- select_leAll

{-@ automatic-instances select_leAll @-}
{-@
select_leAll ::
  {xs:List | 0 < length xs} ->
  LeAll {hd (select xs)} {tl (select xs)}
@-}
select_leAll :: List -> LeAll
select_leAll (Cons x Nil) y = trivial
{-
G: contains (tl (select xs)) y => y <= hd (select xs)

if H1: x1 <= x2 then
  let (Cons x' xs') = select (Cons x1 xs) in
  G: contains (Cons x2 xs') y => x' <= y
  if H2: contains (Cons x2 xs') y then
    G: x' <= y
    H2: \z -> contains xs' z => x' <= z // select_leAll (Cons x1 xs)
    H3: y == x2 || contains xs' y // contains_cons (Cons x2 xs') y
    if H4: y == x2 then
        p: Permuted {Cons x1 xs} {Cons x' xs'} := permuted_select (Cons x1 xs)
        H5: x1 == x' || contains xs' x1 //
          contains_cons
          (Cons x' xs')
            (x1 `by` contains_permuted (Cons x1 xs) (Cons x' xs') p
                      (x1 `with` hd (Cons x1 xs)))
        if H6: x1 == x' then
          H7: x' <= x1 // H6
          H8: x' <= x2 // H1, H7
          G:  x' <= y  // H4, H8
        else H6: contains xs' x1
          H7: x' <= x1 // H2 x1 i.e. select_leAll (Cons x1 xs) x1
          H8: x' <= x2 // H1, H7
          G:  x' <= y  // H4, H8
    else H4: contains xs' y
      G: x' <= y // H2 y i.e. select_leAll (Cons x1 xs) y
  else H2: not (contains (Cons x2 xs') y)
    G: True // trivial
else H1: x2 < x1
  let (Cons x' xs') = select (Cons x2 xs) in
  G: x' <= y
  if H2: contains (Cons x1 xs') y then
      G: x' <= y
      H2: \z -> contains xs' z => x' <= z // select_leAll (Cons x2 xs)
      H3: y == x1 || contains xs' y // contains_cons (Cons x1 xs') y
      if H4: y == x1 then
        p: Permuted {Cons x2 xs} {Cons x' xs'} := permuted_select (Cons x2 xs)
        H5: x1 == x' || contains xs' x2 //
          contains_cons
          (Cons x' xs')
            (x2 `by` contains_permuted (Cons x2 xs) (Cons x' xs') p
                      (x2 `with` hd (Cons x2 xs)))
        if H6: x2 == x' then
          H7: x' <= x2 // H6
          H8: x' <= x1 // H1, H7
          G:  x' <= y  // H4, H8
        else H6: contains xs' x2
          H7: x' <= x2 // H2 x1 i.e. select_leAll (Cons x2 xs)
          H8: x' <= x1 // H1, H7
          G:  x' <= y  // H4, H8
      else H4: contains xs' y
        G: x' <= y // H2 y i.e. select_leAll (Cons x2 xs)
    else H2: not (contains (Cons x2 xs') y)
      G: True // trivial
-}
select_leAll (Cons x1 (Cons x2 xs)) y =
  if x1 <= x2 -- H1
    then
      let (Cons x' xs') = select (Cons x1 xs)
       in if contains (Cons x2 xs') y
            then -- H2

              if y == x2
                then -- H4

                  if x1 == x'
                    then -- H6

                      trivial
                        `by` contains_cons (Cons x2 xs') y
                        `by` select_leAll (Cons x1 xs) x1
                        `by` contains_cons
                          (Cons x' xs')
                          ( x1
                              `by` contains_permuted
                                (Cons x1 xs)
                                (Cons x' xs')
                                (permuted_select (Cons x1 xs))
                                (x1 `with` hd (Cons x1 xs))
                          )
                        `by` contains_permuted
                          (Cons x1 xs)
                          (Cons x' xs')
                          (permuted_select (Cons x1 xs))
                          (x1 `with` hd (Cons x1 xs))
                    else -- H6

                      trivial
                        `by` contains_cons (Cons x2 xs') y
                        `by` select_leAll (Cons x1 xs) x1
                        `by` contains_cons
                          (Cons x' xs')
                          ( x1
                              `by` contains_permuted
                                (Cons x1 xs)
                                (Cons x' xs')
                                (permuted_select (Cons x1 xs))
                                (x1 `with` hd (Cons x1 xs))
                          )
                        `by` contains_permuted
                          (Cons x1 xs)
                          (Cons x' xs')
                          (permuted_select (Cons x1 xs))
                          (x1 `with` hd (Cons x1 xs))
                else -- H4
                  select_leAll (Cons x1 xs) y
            else -- H2
              trivial
    else -- H1

      let (Cons x' xs') = select (Cons x2 xs)
       in if contains (Cons x1 xs') y
            then -- H2

              if y == x1
                then -- H4

                  if x2 == x'
                    then -- H6

                      trivial
                        `by` contains_cons (Cons x1 xs') y
                        `by` select_leAll (Cons x2 xs) x2
                        `by` contains_cons
                          (Cons x' xs')
                          ( x2
                              `by` contains_permuted
                                (Cons x2 xs)
                                (Cons x' xs')
                                (permuted_select (Cons x2 xs))
                                (x2 `with` hd (Cons x2 xs))
                          )
                        `by` contains_permuted
                          (Cons x2 xs)
                          (Cons x' xs')
                          (permuted_select (Cons x2 xs))
                          (x2 `with` hd (Cons x2 xs))
                    else -- H6

                      trivial
                        `by` contains_cons (Cons x1 xs') y
                        `by` select_leAll (Cons x2 xs) x2
                        `by` contains_cons
                          (Cons x' xs')
                          ( x2
                              `by` contains_permuted
                                (Cons x2 xs)
                                (Cons x' xs')
                                (permuted_select (Cons x2 xs))
                                (x2 `with` hd (Cons x2 xs))
                          )
                        `by` contains_permuted
                          (Cons x2 xs)
                          (Cons x' xs')
                          (permuted_select (Cons x2 xs))
                          (x2 `with` hd (Cons x2 xs))
                else -- H4
                  select_leAll (Cons x2 xs) y
            else -- H2
              trivial
