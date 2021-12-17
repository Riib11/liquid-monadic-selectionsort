module QuickSort.MonadicV1 where

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
data List a = Nil | Cons {hd::a, tl::List a}
@-}
-- {-@
-- data List a <p :: Int -> (a -> Bool) -> Bool>
--   = Nil
--   | Cons a<p 0> (List<{\i f -> p (sub1 i) f}> a)
-- @-}
data List a = Nil | Cons a (List a)
  deriving (Eq)

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

{-@ reflect inBounds @-}
inBounds :: Int -> Int -> Bool
inBounds l i = 0 <= i && i < l

{-@
type Ix L = {i:Int | inBounds L i}
@-}
type Ix = Int

{-@ reflect readL @-}
{-@ automatic-instances readL @-}
{-@
readL :: l:Int -> i:Ix {l} -> List a -> Maybe a / [i]
@-}
readL :: Int -> Ix -> List a -> Maybe a
readL l _ Nil = Nothing
readL l i (Cons x xs) =
  if i > 0
    then readL (sub1 l) (sub1 i) xs
    else Just x

{-@ reflect writeL @-}
{-@ automatic-instances writeL @-}
{-@
writeL :: l:Int -> i:Ix {l} -> a -> List a -> Maybe (List a) / [i]
@-}
writeL :: Int -> Ix -> a -> List a -> Maybe (List a)
writeL l i a Nil = Nothing
writeL l i a (Cons x xs) =
  if i > 0 then
    case writeL (sub1 l) (sub1 i) a xs of
      Just xs' -> Just (Cons x xs')
      Nothing -> Nothing
  else
    Just (Cons a xs)

-- Array

-- {-@
-- type Array a P1 P2 = State ({l:List Int | P1 l}) ({l:List Int | P2 l}) a
-- @-}
-- type Array a = State (List Int) (List Int) a

-- {-@
-- type State s1 s2 a = s1 -> Maybe (a, s2)
-- @-}
-- type State s1 s2 a = s1 -> Maybe (a, s2)

{-@
data Array a <p1::List Int -> Bool, p2::List Int -> Bool> = Array ((List Int)<p1> -> Maybe (a, (List Int)<p2>))
@-}
data Array a = Array (List Int -> Maybe (a, List Int))

-- Monad interface

-- {-@
-- returnA :: forall <p::List Int -> Bool>. a -> Array<p, p> a
-- @-}
-- returnA :: a -> Array a
-- returnA a = undefined -- Array $ \xs -> Just (a, xs)

{-@
returnA_aux :: forall <p::List Int -> Bool>. a -> (List Int)<p> -> Maybe (a, (List Int)<p>)
@-}
returnA_aux :: a -> List Int -> Maybe (a, List Int)
returnA_aux a xs = Just (a, xs)

-- {-@
-- bindA :: forall <p1::List Int -> Bool, p2::List Int -> Bool, p3::List Int -> Bool>. Array<p1, p2> a -> (a -> Array<p2, p3> b) -> Array<p1, p3> b
-- @-}
-- bindA :: Array a -> (a -> Array b) -> Array b
-- bindA (Array m) k =
--   Array $ \xs ->
--     case m xs of
--       Just (a, xs') -> case k a of
--         Array m' -> m' xs'
--       Nothing -> Nothing

-- {-@ reflect constant @-}
-- constant :: a -> b -> a
-- constant a _ = a

-- {-@
-- seqA :: forall <p1::List Int -> Bool, p2::List Int -> Bool, p3::List Int -> Bool>. Array<p1, p2> a -> Array<p2, p3> b -> Array <p1, p3> b
-- @-}
-- seqA :: Array a -> Array b -> Array b
-- seqA m1 m2 = bindA m1 (constant m2)

-- -- Failure interface

-- {-@
-- failA :: forall <p1::List Int -> Bool, p2::List Int -> Bool>. Array <p1, p2> a
-- @-}
-- failA :: Array a
-- failA = undefined -- TODO: Array $ \_ -> Nothing

-- -- State interface

-- {-@
-- getA :: forall <p::List Int -> Bool>. Array<p, p> (List Int)
-- @-}
-- getA :: Array (List Int)
-- getA = Array $ \xs -> Just (xs, xs)

-- {-@
-- putA :: forall <p::List Int -> Bool>. (List Int)<p> -> Array<p, p> Unit
-- @-}
-- putA :: List Int -> Array Unit
-- putA xs = Array $ \_ -> Just (unit, xs)

-- -- -- Array interface

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

-- -- -- quickpartition

-- -- -- bounds invariants:
-- -- -- - iHi <= iLo
-- -- -- - iLo <= iP
-- -- {-@ automatic-instances quickpartition @-}
-- -- {-@
-- -- quickpartition ::
-- --   l:Int ->
-- --   iLf:Ix {l} ->
-- --   iLo:{iLo:Ix {l} | iLf <= iLo} ->
-- --   iHi:{iHi:Ix {l} | iLf <= iHi && iHi <= iLo} ->
-- --   iP:{iP:Ix {l} | iLo <= iP} ->
-- --   Array ({iP':Ix {l} | iLf <= iP' && iP' <= iP}) / [iP - iLo]
-- -- @-}
-- -- quickpartition :: Int -> Ix -> Ix -> Ix -> Int -> Array Ix
-- -- quickpartition l iLf iLo iHi iP =
-- --   if iLo < iP then
-- --     bindA (readA l iLo) $ \lo ->
-- --       bindA (readA l iP) $ \p ->
-- --         if lo > p then
-- --           quickpartition l iLf (add1 iLo) iHi iP
-- --         else
-- --           swap l iLo iHi `seqA`
-- --           quickpartition l iLf (add1 iLo) (add1 iHi) iP
-- --   else
-- --     swap l iHi iP `seqA`
-- --     returnA iHi

-- -- -- quicksort

-- -- {-@
-- -- quicksort' ::
-- --   l:Int -> i:Ix {l} -> j:Ix {l} ->
-- --   (List Int -> Maybe (Unit, List Int)) / [j - i]
-- -- @-}
-- -- quicksort' :: Int -> Ix -> Ix -> Array Unit
-- -- quicksort' l i j =
-- --   if i < j then
-- --     bindA (quickpartition l i i i j) $ \iP ->
-- --       seqA
-- --         (if 0 <= sub1 iP - i && sub1 iP - i < j - i && inBounds l (sub1 iP) then quicksort' l i (sub1 iP) else returnA unit)
-- --         (if 0 <= j - add1 iP && j - add1 iP < j - i && inBounds l (add1 iP) then quicksort' l (add1 iP) j else returnA unit)
-- --   else 
-- --     returnA unit

-- -- {-@ automatic-instances quicksort @-}
-- -- {-@
-- -- quicksort :: List Int -> Maybe (Unit, List Int)
-- -- @-}
-- -- quicksort :: List Int -> Maybe (Unit, List Int)
-- -- quicksort xs =
-- --   if lng xs <= 0 then
-- --     Just (unit, xs)
-- --   else
-- --     quicksort' (lng xs) 0 (sub1 (lng xs)) xs

-- -- -- test :: Maybe (Unit, List Int)
-- -- -- test = do
-- -- --   let ls = toList [7,6,5,1,2,4,3,1,1]
-- -- --   -- let ls = toList [7,6,5,4,3,2,1]
-- -- --   quicksort ls
  
-- -- -- delete :: Int -> [Int] -> [Int]
-- -- -- delete x [] = []
-- -- -- delete x (y:ys) = if x == y then ys else y : delete x ys 

-- -- -- permutations :: [Int] -> [[Int]]
-- -- -- permutations [] = [[]]
-- -- -- permutations xs = do
-- -- --   x <- xs
-- -- --   let xs' = delete x xs
-- -- --   xs'' <- permutations xs'
-- -- --   return (x : xs'')
  
-- -- -- qs :: [Int] -> Maybe (List Int)
-- -- -- qs xs = 
-- -- --   case quicksort (toList xs) of
-- -- --     Just (_, xs') -> Just xs' 
-- -- --     Nothing -> Nothing

-- -- -- testN n = 
-- -- --   let ls = [1..n] in
-- -- --   all (== True) (map (== Just (toList ls)) [ qs xs | xs <- permutations ls ])

-- -- -- main :: IO ()
-- -- -- main = do
-- -- --   let f n = putStrLn $ "sorts all singleton lists of length " ++ show n ++ ": " ++ show (testN n)
-- -- --   mapM_ f [0..7]