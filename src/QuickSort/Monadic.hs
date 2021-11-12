module QuickSort.Monadic where

import Proof
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

toList :: [a] -> List a
toList [] = Nil
toList (x : xs) = Cons x (toList xs)

instance Show a => Show (List a) where
  show Nil = "[]"
  show (Cons x xs) = show x ++ ":" ++ show xs

{-@
type Ix L = {i:Int | 0 <= i && i < L}
@-}
type Ix = Int

{-@ reflect readL @-}
{-@
readL :: l:Int -> i:Ix {l} -> List a -> Maybe a / [i]
@-}
readL :: Int -> Ix -> List a -> Maybe a
readL l _ Nil = Nothing
readL l i (Cons x xs) =
  if i == 0
    then Just x
    else readL l (i - 1) xs

{-@ reflect writeL @-}
{-@
writeL :: l:Int -> i:Ix {l} -> a -> List a -> Maybe (List a) / [i]
@-}
writeL :: Int -> Ix -> a -> List a -> Maybe (List a)
writeL l i a Nil = Nothing
writeL l i a (Cons x xs) =
  if i == 0
    then Just (Cons a xs)
    else case writeL l (i - 1) a xs of
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

{-@ reflect constant @-}
constant :: a -> b -> a
constant a _ = a

{-@ reflect seqA @-}
seqA :: Array a -> Array b -> Array b
seqA m1 m2 = bindA m1 (constant m2)

-- Failure inferface

{-@ reflect failA @-}
failA :: Array a
failA xs = Nothing

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
readA :: l:Int -> i:Ix {l} -> Array Int
@-}
readA :: Int -> Ix -> Array Int
readA l i xs =
  case readL l i xs of
    Nothing -> Nothing
    Just x -> Just (x, xs)

-- TODO: not sure why I need to expand `Array Unit` here
{-@ reflect writeA @-}
{-@
writeA :: l:Int -> i:Ix {l} -> Int -> (List Int -> Maybe (Unit, List Int))
@-}
writeA :: Int -> Ix -> Int -> Array Unit
writeA l i y xs =
  case writeL l i y xs of
    Nothing -> Nothing
    Just xs' -> Just (unit, xs')

-- swap

{-@ reflect swap @-}
{-@
swap :: l:Int -> Ix {l} -> Ix {l} -> (List Int -> Maybe (Unit, List Int))
@-}
swap :: Int -> Ix -> Ix -> Array Unit
swap l i j = bindA (readA l i) (swap_aux1 l i j)

{-@ reflect swap_aux1 @-}
{-@
swap_aux1 :: l:Int -> Ix {l} -> Ix {l} -> Int -> (List Int -> Maybe (Unit, List Int))
@-}
swap_aux1 :: Int -> Ix -> Ix -> Int -> Array Unit
swap_aux1 l i j x = bindA (readA l j) (swap_aux2 l i j x)

{-@ reflect swap_aux2 @-}
{-@
swap_aux2 :: l:Int -> Ix {l} -> Ix {l} -> Int -> Int -> (List Int -> Maybe (Unit, List Int))
@-}
swap_aux2 :: Int -> Ix -> Ix -> Int -> Int -> Array Unit
swap_aux2 l i j x y = seqA (writeA l j x) (writeA l i y)

-- quickpartition

{-@ reflect quickpartition_bounds @-}
{-@
quickpartition_bounds :: l:Int -> il:Ix {l} -> ih:Ix {l} -> i:Ix {l} -> im:Ix {l} -> p:Int -> Bool
@-}
quickpartition_bounds :: Int -> Ix -> Ix -> Ix -> Ix -> Int -> Bool
quickpartition_bounds l il ih i im p =
  if i < sub1 im
    then add1 ih < l && add1 i < l
    else add1 ih < l

{-@
quickpartition ::
  l:Int -> il:Ix {l} -> ih:Ix {l} -> i:Ix {l} -> im:Ix {l} -> p:Int ->
  {_:Proof | quickpartition_bounds l il ih i im p} ->
  Array (Ix {l}) / [l - i]
@-}
quickpartition :: Int -> Ix -> Ix -> Ix -> Ix -> Int -> Proof -> Array Ix
quickpartition l il ih i im p _ =
  if i < sub1 im
    then bindA (readA l i) $ \x ->
      if x <= p
        then
          seqA
            (swap l i ih)
            ( (quickpartition l il (add1 ih) (add1 i) im p)
                (assume (quickpartition_bounds l il (add1 ih `by` assume (add1 ih < l)) (add1 i) im p))
            )
        else
          (quickpartition l il ih (add1 i) im p)
            (assume (quickpartition_bounds l il ih (add1 i) im p))
    else seqA (swap l ih i) (returnA (add1 ih))

-- quicksort

{-@ lazy quicksort @-}
{-@
quicksort ::
  l:Int -> i:Ix {l} -> j:Ix {l} ->
  (List Int -> Maybe (Unit, List Int)) / [j - i]
@-}
quicksort :: Int -> Ix -> Ix -> Array Unit
quicksort l i j =
  if i < j
    then bindA (readA l (sub1 j)) $ \p ->
      bindA
        ( (quickpartition l i i i j p)
            (assume (quickpartition_bounds l i i i j p))
        )
        $ \ip ->
          bindA (quicksort l i ip) $ \_ ->
            quicksort l ip j
    else returnA unit

{-@ lazy test @-}
{-@
test :: l:Int -> i:Ix {l} -> j:Ix {l} -> Array (Ix {l})
@-}
test :: Int -> Ix -> Ix -> Array Ix
test l i j =
  if i < j
    then bindA (readA l (sub1 j)) $ \p ->
      (quickpartition l i i i j p)
        (assume (quickpartition_bounds l i i i j p))
    else failA

runQuicksort :: List Int -> Maybe (List Int)
runQuicksort xs =
  let l = lng xs
   in if lng xs <= 0
        then Just xs
        else case quicksort l 0 (sub1 l) xs of
          Just (_, xs') -> Just xs'
          Nothing -> Nothing
