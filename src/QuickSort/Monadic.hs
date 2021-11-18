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
type State s a = s -> (Maybe (a, s), [String])
@-}
type State s a = s -> (Maybe (a, s), [String])

-- Monad interface

-- {-@ reflect returnA @-}
returnA :: a -> Array a
returnA a ls = (Just (a, ls), [])

-- {-@ reflect bindA @-}
bindA :: Array a -> (a -> Array b) -> Array b
bindA m k xs =
  case m xs of
    (Just (a, xs'), ms) ->
      case k a xs' of
        (Just (b, xs''), ms') -> (Just (b, xs''), ms ++ ms')
        (Nothing, ms') -> (Nothing, ms ++ ms')
    (Nothing, ms)-> (Nothing, ms)

-- {-@ reflect constant @-}
constant :: a -> b -> a
constant a _ = a

-- {-@ reflect seqA @-}
seqA :: Array a -> Array b -> Array b
seqA m1 m2 = bindA m1 (constant m2)

-- Failure inferface

-- {-@ reflect failA @-}
failA :: Array a
failA xs = (Nothing, [])

-- State interface

-- {-@ reflect getA @-}
getA :: Array (List Int)
getA xs = (Just (xs, xs), [])

-- {-@ reflect putA @-}
putA :: List Int -> Array Unit
putA xs _ = (Just (unit, xs), [])

-- Array interface

-- {-@ reflect readA @-}
{-@
readA :: l:Int -> i:Ix {l} -> Array Int
@-}
readA :: Int -> Ix -> Array Int
readA l i xs =
  case readL l i xs of
    Nothing -> (Nothing, [])
    Just x -> (Just (x, xs), [])

-- TODO: not sure why I need to expand `Array Unit` here
-- {-@ reflect writeA @-}
{-@
writeA :: l:Int -> i:Ix {l} -> Int -> (List Int -> (Maybe (Unit, List Int), [String]))
@-}
writeA :: Int -> Ix -> Int -> Array Unit
writeA l i y xs =
  case writeL l i y xs of
    Nothing -> (Nothing, [])
    Just xs' -> (Just (unit, xs'), [])

-- notesA

{-@
notesA :: [String] -> Array Unit
@-}
notesA :: [String] -> Array Unit
notesA ms xs = (Just (unit, xs), ms)

-- snapshot

snapshot :: Array Unit
snapshot xs = (Just (unit, xs), [show xs])

{-@
indent :: Int -> String
@-}
indent :: Int -> String
indent i = if i <= 0 then "" else "  " ++ indent (i - 1)

{-@
snapshotPartition :: l:Int -> Ix {l} -> Ix {l} -> Ix {l} -> Array Unit
@-}
snapshotPartition :: Int -> Ix -> Ix -> Ix -> Array Unit
snapshotPartition l iLo iHi iP =
  snapshot `seqA`
  if iLo < iHi then
    notesA
      [ indent iLo ++ "l" ++
        indent (iHi - iLo - 1 `by` undefined) ++ " " ++ "h" ++
        indent (iP - iHi - 1 `by` undefined) ++ " " ++ "p" ]
  else
    if iLo == iHi then
      notesA ["iLo = iHi"]
    else
      notesA ["iLo > iHi"]

{-@
snapshotSort :: l:Int -> Ix {l} -> Ix {l} -> Array Unit
@-}
snapshotSort :: Int -> Ix -> Ix -> Array Unit
snapshotSort l i j =
  snapshot `seqA`
  if i < j then
    notesA
      [ indent i ++ "i" ++
        indent (j - i - 1 `by` undefined) ++ " " ++ "j" ]
  else
    notesA ["i < j :: " ++ show i ++ " < " ++ show j]

-- swap

-- {-@ reflect swap @-}
{-@
swap :: l:Int -> Ix {l} -> Ix {l} -> (List Int -> (Maybe (Unit, List Int), [String]))
@-}
swap :: Int -> Ix -> Ix -> Array Unit
swap l i j = bindA (readA l i) (swap_aux1 l i j)

-- {-@ reflect swap_aux1 @-}
{-@
swap_aux1 :: l:Int -> Ix {l} -> Ix {l} -> Int -> (List Int -> (Maybe (Unit, List Int), [String]))
@-}
swap_aux1 :: Int -> Ix -> Ix -> Int -> Array Unit
swap_aux1 l i j x = bindA (readA l j) (swap_aux2 l i j x)

-- {-@ reflect swap_aux2 @-}
{-@
swap_aux2 :: l:Int -> Ix {l} -> Ix {l} -> Int -> Int -> (List Int -> (Maybe (Unit, List Int), [String]))
@-}
swap_aux2 :: Int -> Ix -> Ix -> Int -> Int -> Array Unit
swap_aux2 l i j x y = seqA (writeA l j x) (writeA l i y)

-- quickpartition

-- {-@ reflect quickpartition_bounds @-}
-- {-@
-- quickpartition_bounds :: l:Int -> iLo:Ix {l} -> iHi:Ix {l} -> i:Ix {l} -> iEnd:Ix {l} -> p:Int -> Bool
-- @-}
-- quickpartition_bounds :: Int -> Ix -> Ix -> Ix -> Ix -> Int -> Bool
-- quickpartition_bounds l iLo iHi i iEnd p =
--   if i < sub1 iEnd
--     then add1 iHi < l && add1 i < l
--     else add1 iHi < l

-- bounds invariants:
-- - iLo <= iHi
-- - iLo < iP
-- - iHi < iP
{-@ lazy quickpartition @-}
{-@
quickpartition ::
  l:Int -> iLo:Ix {l} -> iHi:Ix {l} -> iP:Ix {l} -> 
  Array (Ix {l}) / []
@-}
quickpartition :: Int -> Ix -> Ix -> Int -> Array Ix
quickpartition l iLo iHi iP =
  notesA [unwords ["PART", show iLo, show iHi, show iP]] `seqA`
  snapshot `seqA`
  notesA ["CHECK: iLo < iP: " ++ show (iLo < iP)] `seqA`
  if iLo < iP then
    bindA (readA l iLo) $ \lo ->
      bindA (readA l iP) $ \p ->
        if lo > p then
          notesA ["CASE: lo > p"] `seqA`
          quickpartition l (add1 iLo `by` undefined) iHi iP
        else
          notesA ["CASE: p <= lo"] `seqA`
          swap l iLo iHi `seqA`
          quickpartition l (add1 iLo `by` undefined) (add1 iHi `by` undefined) iP
  else
    notesA ["CASE: iLo < iP"] `seqA`
    notesA [unwords ["SWAP", show iHi, show iP]] `seqA`
    swap l iHi iP `seqA`
    returnA iHi

-- quicksort

-- bounds invariants:
-- - i <= j
{-@ lazy quicksort @-}
{-@
quicksort ::
  l:Int -> i:Ix {l} -> j:Ix {l} ->
  (List Int -> (Maybe (Unit, List Int), [String])) / [j - i]
@-}
quicksort :: Int -> Ix -> Ix -> Array Unit
quicksort l i j =
  notesA [unwords ["SORT", show i, show j]] `seqA`
  snapshot `seqA`
  if i < j
    then
      (bindA (quickpartition l i i j) $ \iP ->
        seqA
          (quicksort l i (sub1 iP `by` undefined))
          (quicksort l (add1 iP `by` undefined) j))
    else 
      returnA unit

runQuicksort :: List Int -> Maybe (List Int)
runQuicksort xs =
  let l = lng xs
   in if lng xs <= 0
        then Just xs
        else case quicksort l 0 0 xs of
          (Just (_, xs'), ms) -> Just xs'
          (Nothing, ms) -> Nothing

test :: IO ()
test = do
  let ls = toList [7,6,5,1,2,4,3,1,1]
  -- let ls = toList [7,6,5,4,3,2,1]
  -- let Just (_, ls', ms) = quickpartition 5 0 0 4 ls
  let (res, ms) = quicksort (lng ls) 0 (sub1 (lng ls)) ls
  case res of
    Just (_, ls') -> do
      putStrLn (unlines ms)
      print ls'
    Nothing -> do
      putStrLn (unlines ms)
      putStrLn "FAILURE"
  
-- quicksort 5 0 4 (toList [5,1,2,4,3])