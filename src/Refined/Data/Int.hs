module Refined.Data.Int where

{-@ reflect le @-}
le :: Int -> Int -> Bool
le x y = x <= y

{-@ reflect eq @-}
eq :: Int -> Int -> Bool
eq x y = x == y

{-@ reflect add1 @-}
add1 :: Int -> Int
add1 x = x + 1

{-@ reflect sub1 @-}
sub1 :: Int -> Int
sub1 x = x - 1
