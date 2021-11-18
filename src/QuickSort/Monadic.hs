{-@ LIQUID "--compile-spec" @-}
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
  deriving (Eq)

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
    else case writeL l (sub1 i) a xs of
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

-- {-@ reflect returnA @-}
returnA :: a -> Array a
returnA a ls = Just (a, ls)

-- {-@ reflect bindA @-}
bindA :: Array a -> (a -> Array b) -> Array b
bindA m k xs =
  case m xs of
    Just (a, xs') -> k a xs'
    Nothing -> Nothing 

-- {-@ reflect constant @-}
constant :: a -> b -> a
constant a _ = a

-- {-@ reflect seqA @-}
seqA :: Array a -> Array b -> Array b
seqA m1 m2 = bindA m1 (constant m2)

-- Failure inferface

-- {-@ reflect failA @-}
failA :: Array a
failA xs = Nothing

-- State interface

-- {-@ reflect getA @-}
getA :: Array (List Int)
getA xs = Just (xs, xs)

-- {-@ reflect putA @-}
putA :: List Int -> Array Unit
putA xs _ = Just (unit, xs)

-- Array interface

-- {-@ reflect readA @-}
{-@
readA :: l:Int -> i:Ix {l} -> Array Int
@-}
readA :: Int -> Ix -> Array Int
readA l i xs =
  case readL l i xs of
    Nothing -> Nothing
    Just x -> Just (x, xs)

-- TODO: not sure why I need to expand `Array Unit` here
-- {-@ reflect writeA @-}
{-@
writeA :: l:Int -> i:Ix {l} -> Int -> (List Int -> Maybe (Unit, List Int))
@-}
writeA :: Int -> Ix -> Int -> Array Unit
writeA l i y xs =
  case writeL l i y xs of
    Nothing -> Nothing
    Just xs' -> Just (unit, xs')

-- swap

-- {-@ reflect swap @-}
{-@
swap :: l:Int -> Ix {l} -> Ix {l} -> (List Int -> Maybe (Unit, List Int))
@-}
swap :: Int -> Ix -> Ix -> Array Unit
swap l i j = bindA (readA l i) (swap_aux1 l i j)

-- {-@ reflect swap_aux1 @-}
{-@
swap_aux1 :: l:Int -> Ix {l} -> Ix {l} -> Int -> (List Int -> Maybe (Unit, List Int))
@-}
swap_aux1 :: Int -> Ix -> Ix -> Int -> Array Unit
swap_aux1 l i j x = bindA (readA l j) (swap_aux2 l i j x)

-- {-@ reflect swap_aux2 @-}
{-@
swap_aux2 :: l:Int -> Ix {l} -> Ix {l} -> Int -> Int -> (List Int -> Maybe (Unit, List Int))
@-}
swap_aux2 :: Int -> Ix -> Ix -> Int -> Int -> Array Unit
swap_aux2 l i j x y = seqA (writeA l j x) (writeA l i y)

-- quickpartition

-- bounds invariants:
-- - iHi <= iLo
-- - iLo <= iP
-- - iHi <= iP
{-@ lazy quickpartition @-}
{-@
quickpartition ::
  l:Int -> iLo:Ix {l} -> iHi:Ix {l} -> iP:Ix {l} -> 
  Array (Ix {l}) / []
@-}
quickpartition :: Int -> Ix -> Ix -> Int -> Array Ix
quickpartition l iLo iHi iP =
  if iLo < iP then
    bindA (readA l iLo) $ \lo ->
      bindA (readA l iP) $ \p ->
        if lo > p then
          quickpartition l (add1 iLo `by` undefined) iHi iP
        else
          swap l iLo iHi `seqA`
          quickpartition l (add1 iLo `by` undefined) (add1 iHi `by` undefined) iP
  else
    swap l iHi iP `seqA`
    returnA iHi

-- quicksort

-- bounds invariants:
-- - i <= j
{-@ lazy quicksort' @-}
{-@
quicksort' ::
  l:Int -> i:Ix {l} -> j:Ix {l} ->
  (List Int -> Maybe (Unit, List Int)) / [j - i]
@-}
quicksort' :: Int -> Ix -> Ix -> Array Unit
quicksort' l i j =
  if i < j
    then
      (bindA (quickpartition l i i j) $ \iP ->
        seqA
          (quicksort' l i (sub1 iP `by` undefined))
          (quicksort' l (add1 iP `by` undefined) j))
    else 
      returnA unit

{-@ lazy quicksort @-}
{-@
quicksort :: List Int -> Maybe (Unit, List Int)
@-}
quicksort :: List Int -> Maybe (Unit, List Int)
quicksort xs = quicksort' (lng xs) 0 (sub1 (lng xs)) xs

test :: Maybe (Unit, List Int)
test = do
  let ls = toList [7,6,5,1,2,4,3,1,1]
  -- let ls = toList [7,6,5,4,3,2,1]
  quicksort ls
  
delete :: Int -> [Int] -> [Int]
delete x [] = []
delete x (y:ys) = if x == y then ys else y : delete x ys 

permutations :: [Int] -> [[Int]]
permutations [] = [[]]
permutations xs = do
  x <- xs
  let xs' = delete x xs
  xs'' <- permutations xs'
  return (x : xs'')
  
qs :: [Int] -> Maybe (List Int)
qs xs = 
  case quicksort (toList xs) of
    Just (_, xs') -> Just xs' 
    Nothing -> Nothing

testN n = 
  let ls = [1..n] in
  all (== True) (map (== Just (toList ls)) [ qs xs | xs <- permutations ls ])

main :: IO ()
main = do
  let f n = putStrLn $ "sorts all singleton lists of length " ++ show n ++ ": " ++ show (testN n)
  mapM_ f [0..7]