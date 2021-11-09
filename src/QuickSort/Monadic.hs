module QuickSort.Monadic where

import Refined.Data.Unit

-- Note that, unfortunately, some of the names are weird in order to avoid
-- clashing with Prelude names (e.g. `length`) or LH's refined Prelude (e.g.
-- `len`)

-- Int

{-@ reflect add1 @-}
add1 :: Int -> Int
add1 x = x + 1

{-@ reflect sub1 @-}
sub1 :: Int -> Int
sub1 x = x - 1

-- List

{-@
data List a <p :: a -> a -> Bool> = Nil | Cons {hd::a, tl::List (a<p hd>)}
@-}
data List a = Nil | Cons a (List a)

{-@
type ListSorted = List<{\h v -> h <= v}> Int
@-}
type ListSorted = List Int

{-@ measure lng @-}
lng :: List a -> Int
lng Nil = 0
lng (Cons _ xs) = 1 + lng xs

{-@
type Ix = {i:Int | 0 <= i}
@-}
type Ix = Int

{-@ reflect readL @-}
{-@
readL :: i:Ix -> List a -> Maybe a / [i]
@-}
readL :: Ix -> List a -> Maybe a
readL _ Nil = Nothing
readL i (Cons x xs) =
  if i == 0
    then Just x
    else readL (i - 1) xs

{-@ reflect writeL @-}
{-@
writeL :: i:Ix -> a -> List a -> Maybe (List a) / [i]
@-}
writeL :: Ix -> a -> List a -> Maybe (List a)
writeL i a Nil = Nothing
writeL i a (Cons x xs) =
  if i == 0
    then Just (Cons a xs)
    else case writeL (i + 1) a xs of
      Just xs' -> Just (Cons x xs')
      Nothing -> Nothing

-- Array

{-@
type Array a = State (List Int) a
@-}
type Array a = State (List Int) a

{-@
type ArraySorted a = State (List<{\h v -> h <= v}> Int) a
@-}
type ArraySorted a = Array a

{-@
type State s a = s -> Maybe (a, s)
@-}
type State s a = s -> Maybe (a, s)

-- Monad interface

{-@ reflect returnA @-}
returnA :: a -> Array a
returnA a ls = Just (a, ls)

{-@ reflect bindA @-}
bindA :: Array a -> (a -> Array b) -> Array b
bindA m k xs =
  case m xs of
    Just (a, xs') -> k a xs'
    Nothing -> Nothing

-- State interface

{-@ reflect getA @-}
getA :: Array (List Int)
getA xs = Just (xs, xs)

{-@ reflect putA @-}
putA :: List Int -> Array Unit
putA xs _ = Just (unit, xs)

-- Array interface

{-@ reflect readA @-}
{-@
readA :: i:Ix -> Array Int
@-}
readA :: Ix -> Array Int
readA i xs =
  case readL i xs of
    Nothing -> Nothing
    Just x -> Just (x, xs)

-- TODO: not sure why I need to expand `Array Unit` here
{-@ reflect writeA @-}
{-@
writeA :: i:Ix -> Int -> (List Int -> Maybe (Unit, List Int))
@-}
writeA :: Ix -> Int -> Array Unit
writeA i y xs = Just (unit, xs)

-- quicksort

{-@
quicksort :: Array Unit
@-}
quicksort :: Array Unit
quicksort = undefined
