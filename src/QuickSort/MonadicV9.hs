{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}
{-@ LIQUID "--ple" @-}

module QuickSort.MonadicV9 where

import Refined.Data.Unit
import Refined.Function
import Relation.Equality.Leibniz

type Ix = Int

class Array (m :: * -> *) where
  {-@
  pureArray :: forall a. a -> m a
  @-}
  pureArray :: forall a. a -> m a

  {-@
  bindArray :: forall a b. m a -> (a -> m b) -> m b
  @-}
  bindArray :: forall a b. m a -> (a -> m b) -> m b

  {-@
  readArray :: Ix -> m Int
  @-}
  readArray :: Ix -> m Int

  {-@
  writeArray :: (Ix, Int) -> m Unit
  @-}
  writeArray :: (Ix, Int) -> m Unit

  {-@
  size :: m Ix
  @-}
  size :: m Ix

{-@ reflect seqArray @-}
seqArray :: forall m a b. Array m => m a -> m b -> m b
seqArray ma mb = bindArray ma (constant mb)

{-@ reflect mapArray @-}
mapArray :: forall m a b. Array m => (a -> b) -> (m a -> m b)
mapArray f ma = bindArray ma (mapArray_aux f)

{-@ reflect mapArray_aux @-}
mapArray_aux :: forall m a b. Array m => (a -> b) -> a -> m b
mapArray_aux f a = pureArray (f a)

-- TODO: infinite loop... but how to keep track of last index?
{-@ reflect getArray_aux1 @-}
getArray_aux1 :: Array m => Ix -> m [Int]
getArray_aux1 i =
  bindArray
    (readArray i)
    (getArray_aux2 i)

{-@ reflect getArray_aux2 @-}
getArray_aux2 :: Array m => Ix -> Int -> m [Int]
getArray_aux2 i e =
  bindArray
    (getArray_aux1 (i + 1))
    (getArray_aux3 e)

{-@ reflect getArray_aux3 @-}
getArray_aux3 :: Array m => Int -> [Int] -> m [Int]
getArray_aux3 e es = pureArray (e : es)

-- swap

{-@ reflect swap @-}
swap :: Array m => (Ix, Ix) -> m Unit
swap (i, j) = bindArray (readArray i) (swap_aux1 (i, j))

{-@ reflect swap_aux1 @-}
swap_aux1 :: Array m => (Ix, Ix) -> Int -> m Unit
swap_aux1 (i, j) x = bindArray (readArray j) (swap_aux2 (i, j) x)

{-@ reflect swap_aux2 @-}
swap_aux2 :: Array m => (Ix, Ix) -> Int -> Int -> m Unit
swap_aux2 (i, j) x y = seqArray (writeArray (j, x)) (writeArray (i, y))

-- |
-- == Array Permutation

{-@
type Permutation m A = Equal (Int -> m Int) {permutation_aux A} {countArray}
@-}
type Permutation m = Equal (Int -> m Int)

{-@ reflect permutation_aux @-}
permutation_aux :: Array m => m a -> Int -> m Int
permutation_aux m e = seqArray m (countArray e)

{-@ reflect count @-}
count :: Eq a => a -> [a] -> Int
count _ [] = 0
count a (a' : as) = if a == a' then 1 + count a as else count a as

{-@ reflect getArray :: Array m => m [Int] @-}
getArray :: Array m => m [Int]
getArray = getArray_aux1 0

{-@ reflect countArray @-}
countArray :: Array m => Int -> m Int
countArray e = mapArray (count e) getArray

-- swap_permutation

{-@
swap_permutation :: forall m. Array m => i:Ix -> j:Ix -> Permutation m {swap i j}
@-}
swap_permutation :: forall m. Array m => Ix -> Ix -> Permutation m
swap_permutation i j = undefined

-- {-@ reflect swap_permutation_spec_aux @-}
-- swap_permutation_spec_aux :: (Ix, Ix) -> [Int] -> Int -> Int
-- swap_permutation_spec_aux (i, j) = permutation_aux (swap (i, j))
