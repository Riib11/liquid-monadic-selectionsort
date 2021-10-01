{-@ LIQUID "--compile-spec" @-}
module Refined.Data.List where

import Prelude hiding (length, minimum, min, all, any, head, tail)
import Proof

{-@ reflect leq @-}
leq :: Int -> Int -> Bool
leq x y = x <= y

{-@ reflect eq @-}
eq :: Int -> Int -> Bool
eq x y = x == y

-- data List

data List a = Nil | Cons a (List a)
  deriving (Show)

infixr 5 `Cons`

-- List uses length as a termination measure
{-@ data List [length] @-}


-- length

{-@ measure length @-}
{-@ length :: List a -> {l:Int | 0 <= l} @-}
length :: List a -> Int
length Nil = 0
length (Cons x xs) = 1 + length xs


-- head

-- TODO: why can't reflect???
-- {-@ reflect head @-}
{-@
head :: {xs:List a | 0 < length xs} -> a
@-}
head :: List a -> a
head (Cons x xs) = x


-- tail

-- {-@ reflect tail @-}
{-@
tail :: {xs:List a | 0 < length xs} -> List a
@-}
tail :: List a -> List a
tail Nil = Nil
tail (Cons x xs) = xs

-- index

{-@ reflect index @-}
{-@
index :: {i:Int | 0 <= i} -> {xs:List a | i < length xs} -> a
@-}
index :: Int -> List a -> a
index i (Cons x xs) = if i == 0 then x else index (i - 1) xs


-- contains

{-@ reflect contains @-}
contains :: List Int -> Int -> Bool
contains Nil y = False 
contains (Cons x xs) y = if x == y then True else contains xs y

{-@ reflect contains' @-}
contains' :: List Int -> Int -> Bool
contains' xs y = exists (eq y) xs

{-@ automatic-instances contains_cons @-}
{-@
contains_cons :: 
  x:Int -> xs:List Int ->
  {y:Int | contains (Cons x xs) y && not (x == y)} ->
  {contains xs y}
@-}
contains_cons :: Int -> List Int -> Int -> Proof
contains_cons x Nil y = trivial
-- GOAL: if x' == y then True else contains xs y
contains_cons x (Cons x' xs) y =
  if x' == y
    -- GOAL: True
    then trivial
    -- GOAL: contains xs y
    else trivial


-- minimum

{-@ reflect min @-}
{-@
min :: x:Int -> y:Int -> {z:Int | z <= x && z <= y}
@-}
min :: Int -> Int -> Int
min x y = if x <= y then x else y

{-@ reflect minimum @-}
{-@
minimum :: {xs:List Int | 0 < length xs} -> Int
@-}
minimum :: List Int -> Int
minimum (Cons x Nil) = x
minimum (Cons x xs) = min x (minimum xs)

-- -- * PASSES
-- {-@ reflect minimum_leq @-}
{-@ automatic-instances minimum_leq @-}
{-@
minimum_leq ::
  {xs:List Int | 0 < length xs} ->
  {all (leq (minimum xs)) xs}
@-}
minimum_leq :: List Int -> Proof
minimum_leq (Cons x Nil) = trivial
minimum_leq (Cons x1 (Cons x2 Nil)) = trivial
minimum_leq (Cons x1 (Cons x2 xs)) = undefined -- TODO
  -- let m = minimum (Cons x1 (Cons x2 xs)) in
  -- if m == x1 then
  --   -- GOAL: all (leq (min x1 (minimum (Cons x2 xs)))) (Cons x1 (Cons x2 xs))
  --   -- GOAL: leq x1 (min x1 (minimum (Cons x2 xs))) &&
  --   --       all (leq (min x1 (minimum (Cons x2 xs)))) (Cons x2 xs)
  --   trivial
  -- else 
  --   undefined

-- minimum_leq (Cons x xs) =
--   let m = minimum (Cons x xs) in
--   if x == m then
--     trivial
--   else
--     minimum_leq xs

--   if x == y
--     then trivial
--     else unreachable
-- minimum_leq (Cons x xs) y =
--   if x == y
--     then trivial
--     else minimum_leq xs y

-- -- -- * PASSES
-- {-@ reflect minimum_leq @-}
-- {-@ automatic-instances minimum_leq @-}
-- {-@
-- minimum_leq ::
--   {xs:List Int | 0 < length xs} -> {y:Int | contains xs y} ->
--   {minimum xs <= y}
-- @-}
-- minimum_leq :: List Int -> Int -> Proof
-- minimum_leq (Cons x Nil) y =
--   if x == y
--     then trivial
--     else unreachable
-- minimum_leq (Cons x xs) y =
--   if x == y
--     then trivial
--     else minimum_leq xs y

-- * PASSES
{-@ reflect minimum_contains @-}
{-@ automatic-instances minimum_contains @-}
{-@
minimum_contains ::
  {xs:List Int | 0 < length xs} ->
  {contains xs (minimum xs)}
@-}
minimum_contains :: List Int -> Proof
-- GOAL: if x == y then True else contains Nil x
minimum_contains (Cons x Nil) = trivial
-- GOAL: if x == min x (minimum xs) then True else contains xs (min x (minimum xs))
minimum_contains (Cons x xs) =
  if x <= min x (minimum xs)
    -- GOAL: True
    then trivial
    -- GOAL: if x == minimum xs then True else contains xs (minimum xs)
    else
      if x == minimum xs
        then trivial
        else minimum_contains xs

{-@
minimum_permuted ::
  {xs:List Int | 0 < length xs} ->
  {ys:List Int | permuted xs ys} ->
  {minimum xs == minimum ys}
@-}
minimum_permuted :: List Int -> List Int -> Proof
minimum_permuted xs ys = undefined -- TODO



-- singleton

{-@ reflect singleton @-}
singleton :: List Int -> Bool
singleton Nil = True 
singleton (Cons x xs) = if contains xs x then False else singleton xs

{-@ automatic-instances singleton_cons @-}
{-@
singleton_cons ::
  x:Int -> {xs:List Int | singleton xs && not (contains xs x)} ->
  {singleton (Cons x xs)}
@-}
singleton_cons :: Int -> List Int -> Proof 
singleton_cons x xs = trivial

{-@ 
singleton_snoc ::
  x:Int -> {xs:List Int | singleton (Cons x xs)} ->
  {singleton xs}
@-}
singleton_snoc :: Int -> List Int -> Proof
singleton_snoc x xs = undefined

{-@
singleton_without ::
  {xs:List Int | 0 < length xs && singleton xs} -> {x:Int | contains xs x} ->
  {singleton (without xs x)}
@-}
singleton_without :: List Int -> Int -> List Int
singleton_without xs x = undefined


-- without

{-@ reflect without @-}
without :: List Int -> Int -> List Int
without Nil y = Nil
without (Cons x xs) y = if x == y then xs else Cons x (without xs y)

-- {-@
-- without_verified ::
--   {xs:List Int | singleton xs && 0 < length xs} ->
--   {y:Int | contains xs y} ->
--   {xs':List Int | not (contains xs' y) && singleton xs' && length xs' = length xs - 1}
-- @-}
-- without_verified :: List Int -> Int -> List Int
-- without_verified xs y = without xs y

{-@ reflect without_contains'_aux @-}
{-@
without_contains'_aux :: 
  {xs:List Int | singleton xs && 0 < length xs} ->
  {y:Int | contains xs y} ->
  Int ->
  Bool
@-}
without_contains'_aux :: List Int -> Int -> Int -> Bool
without_contains'_aux xs y z = contains (without xs y) z || z == y

{-@ automatic-instances without_contains' @-}
{-@
without_contains' ::
  {xs:List Int | singleton xs && 0 < length xs} ->
  {y:Int | contains xs y} ->
  {all (without_contains'_aux xs y) xs}
@-}
without_contains' :: List Int -> Int -> Proof
without_contains' (Cons x Nil) y = trivial
without_contains' (Cons x xs) y =
  -- GOAL: all (without_contains'_aux (Cons x xs) y) (Cons x xs)
  -- GOAL: (contains (without (Cons x xs) y) x || x == y) && all (without_contains'_aux (Cons x xs) y) xs
  -- GOAL: all (without_contains'_aux (Cons x xs) y) xs
  undefined -- TODO


-- {-@ automatic-instances without_contains @-}
-- {-@
-- without_contains ::
--   {xs:List Int | singleton xs && 0 < length xs} ->
--   {y:Int | contains xs y} -> {z:Int | contains xs z && z /= y} ->
--   {contains (without xs y) z}
-- @-}
-- without_contains :: List Int -> Int -> Int -> Proof
-- without_contains (Cons x Nil) y z =
--   if x == y then
--     trivial
--   else
--     trivial
-- without_contains (Cons x1 (Cons x2 Nil)) y z = 
--   if x1 == y then 
--     if x2 == z
--       then trivial
--       else trivial
--   else
--     if x2 == y then
--       if x1 == z
--         then trivial
--         else trivial
--     else
--       trivial
-- -- GOAL: contains (without (Cons x1 (Cons x2 xs)) y) z
-- without_contains (Cons x1 (Cons x2 xs)) y z =
--   if x1 == y then 
--     if x2 == z then
--       -- GOAL: True
--       trivial
--     else
--       -- GOAL: contains xs z
--       trivial
--   else
--     if x2 == y then
--       -- GOAL: contains (Cons x1 xs) z
--       if x1 == z then 
--         trivial
--       else
--         -- GOAL: contains xs z
--         trivial
--     else
--       -- GOAL: contains (Cons x1 (without xs y)) z
--       if x1 == z then
--         -- GOAL: True 
--         trivial
--       else
--         if x2 == z then
--           trivial
--         else
--           -- GOAL: contains (without xs y) z
--           without_contains xs y z

-- * PASSES
{-@ reflect without_length @-}
{-@ automatic-instances without_length @-}
{-@
without_length ::
  xs:List Int -> {y:Int | contains xs y} ->
  {length (without xs y) == length xs - 1}
@-}
without_length :: List Int -> Int -> Proof
-- CONTRA: contains Nil y == True
without_length Nil y = unreachable
without_length (Cons x xs) y =
  if x == y
    -- GOAL: length xs == length xs
    then ()
    -- GOAL: length (without xs y) == length xs
    else without_length xs y

-- * PASSES
{-@ reflect without_not_contains @-}
{-@ automatic-instances without_not_contains @-}
{-@
without_not_contains ::
  {xs:List Int | singleton xs} -> {y:Int | contains xs y} ->
  {not (contains (without xs y) y)}
@-}
without_not_contains :: List Int -> Int -> Proof
without_not_contains Nil y = unreachable
without_not_contains (Cons x xs) y =
  if x == y
    -- GOAL: not (contains xs y)
    then ()
    -- GOAL: not (contains (without xs y) y)
    else without_not_contains xs y


-- all

{-@ reflect all @-}
all :: (a -> Bool) -> List a -> Bool
all p Nil = True 
all p (Cons x xs) = p x && all p xs


-- any

{-@ reflect any @-}
any :: (a -> Bool) -> List a -> Bool
any p Nil = False
any p (Cons x xs) = p x || any p xs


-- exists

{-@ reflect exists @-}
exists :: (a -> Bool) -> List a -> Bool
exists p Nil = False 
exists p (Cons x xs) = p x || exists p xs


-- permuted

{-@ reflect permuted @-}
permuted :: List Int -> List Int -> Bool
permuted xs ys = all (contains ys) xs

{-@ 
permuted_length :: xs:List Int -> {ys:List Int | permuted xs ys} -> {length xs == length ys}
@-}
permuted_length :: List Int -> List Int -> Proof
permuted_length xs ys = undefined -- TODO