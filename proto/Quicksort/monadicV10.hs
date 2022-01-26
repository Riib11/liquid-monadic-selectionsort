{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}
{-@ LIQUID "--ple" @-}

module QuickSort.MonadicV10 where

import Refined.Data.Unit
import Refined.Function
import Relation.Equality.Leibniz

-- |
-- == Mnd
class Mnd (m :: * -> *) where
  {-@
  pureMnd :: forall a. a -> m a
  @-}
  pureMnd :: forall a. a -> m a

  {-@
  bindMnd :: forall a b. m a -> (a -> m b) -> m b
  @-}
  bindMnd :: forall a b. m a -> (a -> m b) -> m b

-- TODO: monad laws

{-@ reflect seqMnd @-}
seqMnd :: forall m a b. Mnd m => m a -> m b -> m b
seqMnd a1 a2 = bindMnd a1 (constant a2)

-- |
-- == RunArray
class RunArray (m :: * -> *) where
  {-@
  runArray :: forall e a. m a -> [e] -> ([e], a)
  @-}
  runArray :: forall e a. m a -> [e] -> ([e], a)

-- TODO: runArray laws

{-@ reflect execArray @-}
execArray :: forall m e a. RunArray m => m a -> [e] -> [e]
execArray array as = fst $ runArray array as

-- |
-- == Array
class (Mnd m, RunArray m) => Array (m :: * -> *) (i :: *) | i -> m where
  {-@
  readArray :: forall e. i -> array e
  @-}
  readArray :: forall e. i -> m e

  {-@
  writeArray :: forall e. i -> e -> m Unit
  @-}
  writeArray :: forall e. i -> e -> m Unit

-- TODO: array laws

-- -- swap

-- {-@ reflect swap @-}
-- swap :: Array m i => i -> i -> m Unit
-- swap i j = bindMnd (readArray i) (swap_aux1 i j)

-- {-@ reflect swap_aux1 @-}
-- swap_aux1 :: Array m i => i -> i -> e -> m Unit
-- swap_aux1 i j x = bindMnd (readArray j) (swap_aux2 i j x)

-- {-@ reflect swap_aux2 @-}
-- swap_aux2 :: Array m i => i -> i -> e -> e -> m Unit
-- swap_aux2 i j x y = seqMnd (writeArray j x) (writeArray i y)

-- -- -- |
-- -- -- == Array Permutation

-- -- -- {-@
-- -- -- type Permutation array A = Equal ([e] -> e -> Int) {permutation_aux A} {count}
-- -- -- @-}
-- -- -- type Permutation array =

-- {-@ reflect count @-}
-- count :: Eq a => [a] -> a -> Int
-- count [] _ = 0
-- count (a : as) a' = if a == a' then 1 + (count as a') else count as a'

-- -- {-@ reflect permutation_aux @-}
-- -- permutation_aux :: (Array m i, Eq e) => m a -> [e] -> e -> Int
-- -- permutation_aux array as a' = count (execArray array as) a'

-- {-@
-- swap_permutation :: forall m. i:i -> j:i -> Equal ([e] -> e -> Int) {permutation_aux swap} {count}
-- @-}
-- swap_permutation :: forall array. i -> i -> Equal ([e] -> e -> Int)
-- swap_permutation = undefined
