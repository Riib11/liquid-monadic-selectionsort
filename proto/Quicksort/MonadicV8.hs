{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}
{-@ LIQUID "--ple" @-}

module QuickSort.MonadicV8 where

import Refined.Data.Unit
import Refined.Function
import Relation.Equality.Leibniz

i:{i:Int | 0 <= i && i < length array}

class Array (array :: * -> *) where
  type Ix array :: *
  type El array :: *

  {-@
  runArray :: forall a. array a -> [El array] -> ([El array], a)
  @-}
  runArray :: forall a. array a -> [El array] -> ([El array], a)

  {-@
  pureArray :: forall a. a -> array a
  @-}
  pureArray :: forall a. a -> array a

  {-@
  bindArray :: forall a b. array a -> (a -> array b) -> array b
  @-}
  bindArray :: forall a b. array a -> (a -> array b) -> array b

  {-@
  readArray :: Ix array -> array (El array)
  @-}
  readArray :: Ix array -> array (El array)

  {-@
  writeArray :: Ix array -> El array -> array Unit
  @-}
  writeArray :: Ix array -> El array -> array Unit

  {-@
  incIx :: forall a. array a -> Ix array -> Ix array
  @-}
  incIx :: forall a. array a -> Ix array -> Ix array

  {-@
  rangeIx :: forall a. array a -> [Ix array]
  @-}
  rangeIx :: forall a. array a -> [Ix array]

{-@ reflect seqArray @-}
seqArray :: forall array a b. Array array => array a -> array b -> array b
seqArray a1 a2 = bindArray a1 (constant a2)

{-@ reflect execArray @-}
execArray :: forall array a. Array array => array a -> [El array] -> [El array]
execArray array as = fst (runArray array as)

-- swap

{-@ reflect swap @-}
swap :: Array array => Ix array -> Ix array -> array Unit
swap i j = bindArray (readArray i) (swap_aux1 i j)

{-@ reflect swap_aux1 @-}
swap_aux1 :: Array array => Ix array -> Ix array -> El array -> array Unit
swap_aux1 i j x = bindArray (readArray j) (swap_aux2 i j x)

{-@ reflect swap_aux2 @-}
swap_aux2 :: Array array => Ix array -> Ix array -> El array -> El array -> array Unit
swap_aux2 i j x y = seqArray (writeArray j x) (writeArray i y)

-- |
-- == Array Permutation

-- {-@
-- type Permutation array A = Equal ([El array] -> El array -> Int) {permutation_aux A} {count}
-- @-}
-- type Permutation array =

{-@ reflect count @-}
count :: Eq a => [a] -> a -> Int
count [] _ = 0
count (a : as) a' = if a == a' then 1 + (count as a') else count as a'

{-@ reflect permutation_aux @-}
permutation_aux :: (Array array, Eq (El array)) => array a -> [El array] -> El array -> Int
permutation_aux array as a' = count (execArray array as) a'

{-@
swap_permutation :: forall array. i:Ix array -> j:Ix array -> Equal ([El array] -> El array -> Int) {permutation_aux swap} {count}
@-}
swap_permutation :: forall array. Ix array -> Ix array -> Equal ([El array] -> El array -> Int)
swap_permutation = undefined
