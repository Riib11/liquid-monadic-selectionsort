-- {-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}
{-@ LIQUID "--ple" @-}

module QuickSort.MonadicV11 where

import Refined.Data.Unit
import Refined.Function
import Relation.Equality.Leibniz

class Array (m :: * -> *) (i :: *) (e :: *) | i -> m, m -> i, e -> m, m -> e where
  {-@
  pureArray :: forall a. a -> m a
  @-}
  pureArray :: forall a. a -> m a

  {-@
  bindArray :: forall a b. m a -> (a -> m b) -> m b
  @-}
  bindArray :: forall a b. m a -> (a -> m b) -> m b

  {-@
  readArray :: i -> m e
  @-}
  -- readArray :: i:{i:Int | ixFirst <= i && i < ixLast} -> m e
  readArray :: i -> m e

  {-@
  writeArray :: (i, e) -> m Unit
  @-}
  writeArray :: (i, e) -> m Unit

  {-@
  runArray :: forall a. m a -> [e] -> ([e], a)
  @-}
  runArray :: forall a. m a -> [e] -> ([e], a)

  {-@
  ixFirst :: i
  @-}
  ixFirst :: i

  {-@
  ixLast :: i
  @-}
  ixLast :: i

-- TODO: make example that demonstrates this bug
data X

{-@
tmp :: (Array m X) => m e
@-}
tmp :: (Array m X) => m e
tmp = readArray ixFirst

-- {-@ reflect seqArray @-}
-- seqArray :: forall m a b. Array m => m a -> m b -> m b
-- seqArray a1 a2 = bindArray a1 (constant a2)

-- {-@ reflect execArray @-}
-- execArray :: forall m a. Array m => m a -> [e] -> [e]
-- execArray m as = fst (runArray m as)

-- -- swap

-- {-@ reflect swap @-}
-- swap :: Array m => (Ix, Ix) -> m Unit
-- swap (i, j) = bindArray (readArray i) (swap_aux1 (i, j))

-- {-@ reflect swap_aux1 @-}
-- swap_aux1 :: Array m => (Ix, Ix) -> e -> m Unit
-- swap_aux1 (i, j) x = bindArray (readArray j) (swap_aux2 (i, j) x)

-- {-@ reflect swap_aux2 @-}
-- swap_aux2 :: Array m => (Ix, Ix) -> e -> e -> m Unit
-- swap_aux2 (i, j) x y = seqArray (writeArray (j, x)) (writeArray (i, y))

-- -- |
-- -- == Array Permutation

-- {-@ reflect count @-}
-- count :: Eq a => [a] -> a -> e
-- count [] _ = 0
-- count (a : as) a' = if a == a' then 1 + count as a' else count as a'

-- countArray :: Array m => e -> m e

-- countArray

-- {-@ reflect permutation_aux @-}
-- permutation_aux :: Array m => m a -> [e] -> e -> e
-- permutation_aux m as a' = count (execArray m as) a'

-- -- swap_permutation

-- {-@
-- swap_permutation :: forall m. Array m => -> Equal ((Ix, Ix) -> [Int] -> Int -> Int) {swap_permutation_spec_aux} {count}
-- @-}
-- swap_permutation :: forall m. Array m => Equal ((Ix, Ix) -> [Int] -> Int -> Int)
-- swap_permutation i j = undefined -- reflexivity (permutation_aux swap)

-- -- {-@ reflect swap_permutation_spec_aux @-}
-- -- swap_permutation_spec_aux :: (Ix, Ix) -> [Int] -> Int -> Int
-- -- swap_permutation_spec_aux (i, j) = permutation_aux (swap (i, j))
