{-# LANGUAGE AllowAmbiguousTypes #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}
{-@ LIQUID "--ple" @-}

module QuickSort.MonadicV7 where

import Refined.Data.Unit
import Refined.Function

class Array (arr :: * -> *) (i :: *) (e :: *) where
  {-@
  runArray :: forall a. arr a -> [e] -> ([e], a)
  @-}
  runArray :: forall a. arr a -> [e] -> ([e], a)

  {-@
  readArray :: i -> arr e
  @-}
  readArray :: i -> arr e

  {-@
  pureArray :: forall a. a -> arr a
  @-}
  pureArray :: forall a. a -> arr a

  {-@
  bindArray :: forall a b. arr a -> (a -> arr b) -> arr b
  @-}
  bindArray :: forall a b. arr a -> (a -> arr b) -> arr b

  {-@
  writeArray :: i -> e -> arr Unit
  @-}
  writeArray :: i -> e -> arr Unit

{-@ reflect seqArray @-}
seqArray :: forall arr i e a b. Array arr i e => arr a -> arr b -> arr b
seqArray a1 a2 = bindArray a1 (constant a2)

-- -- TODO: include monad and array laws
-- class Array (arr :: * -> * -> * -> *) where
--   {-@
--   runArray :: forall i e a. arr i e a -> [e] -> ([e], a)
--   @-}
--   runArray :: forall i e a. arr i e a -> [e] -> ([e], a)

-- {-@
-- pureArray :: forall i e a. a -> arr i e a
-- @-}
-- pureArray :: forall i e a. a -> arr i e a

-- {-@
-- bindArray :: forall i e a b. arr i e a -> (a -> arr i e b) -> arr i e b
-- @-}
-- bindArray :: forall i e a b. arr i e a -> (a -> arr i e b) -> arr i e b

--   {-@
--   readArray :: forall i e. i -> arr i e e
--   @-}
--   readArray :: forall i e. i -> arr i e e

--   {-@
--   writeArray :: forall i e. Int -> arr i e Unit
--   @-}
--   writeArray :: forall i e. Int -> arr i e Unit

-- {-@ reflect seqArray @-}
-- seqArray :: Array arr => arr i e a -> arr i e b -> arr i e b
-- seqArray a1 a2 = bindArray a1 (constant a2)
