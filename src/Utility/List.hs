module Utility.List where

import Language.Haskell.Liquid.ProofCombinators

-- {-@ reflect index @-}
-- index :: 

-- {-@
-- minimum_safe :: {xs:[Int] | 0 < length xs} -> Int
-- @-}
-- minimum_safe :: [Int] -> Int
-- minimum_safe (x : xs) =
--   if 0 < length xs
--     then min x (minimum_safe xs)
--     else x

-- {-@
-- minimum_safe_correct ::
--   {xs:[Int] | 0 < length xs} -> {i:Int | i < length xs} ->
--   {minimum_safe xs <= xs ! i}
-- @-}
-- minimum_safe_correct :: [Int] -> Int -> ()
-- minimum_safe_correct xs i = undefined

-- {-@
-- minimumIndex :: {xs:[Int] | 0 < length xs} -> Int
-- @-}
-- minimumIndex :: [Int] -> Int
-- minimumIndex xs = undefined

-- {-@
-- minimumIndex_correct ::
--   {xs:[Int] | 0 < length xs} ->
--   {xs !! (minimumIndex xs) == minimum_safe xs}
-- @-}
-- minimumIndex_correct :: [Int] -> ()
-- minimumIndex_correct (x : xs) = ()

-- {-@
-- deleteIndex ::
--   i:Int ->
--   {xs:[Int] | i < length xs} ->
--   {xs':[Int] | length xs = length xs' - 1}
-- @-}
-- deleteIndex :: Int -> [Int] -> [Int]
-- deleteIndex i (x : xs) = if i == 0 then xs else x : deleteIndex (i - 1) xs

-- {-@
-- deleteSafe :: Int -> [Int] -> [Int]
-- @-}
-- deleteSafe :: Int -> [Int] -> [Int]
-- deleteSafe x' [] = []
-- deleteSafe x' (x : xs) = if x == x' then xs else x : deleteSafe x' xs

-- {-@
-- all_safe :: (Int -> Bool) -> [Int] -> Bool
-- @-}
-- all_safe p [] = True 
-- all_safe p (x : xs) = p x && all_safe p xs