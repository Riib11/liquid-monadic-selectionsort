{-# LANGUAGE GADTs, DataKinds, ExplicitForAll #-}
{-@ LIQUID "--no-totality" @-}

module QuickSort.MonadicV3 where

import Proof
-- import Relation.Equality.Prop
import Relation.Equality.Leibniz
import Refined.Data.Unit
import Refined.Data.Int
import Refined.Data.Vec

-- readV

{-@ reflect readV @-}
readV :: Ix n -> Vec (Suc n) e -> e
readV SZero (Cons x xs) = x
readV (SSuc n) (Cons x xs) = readV n xs

-- writeV

{-@ reflect writeV @-}
writeV :: e -> Ix n -> Vec (Suc n) e -> Vec (Suc n) e
writeV a SZero (Cons x xs) = Cons a xs
writeV a (SSuc n) (Cons x xs) = Cons x (writeV a n xs)

-- swapV

-- 1. write xi at j
-- 2. write xj at i
{-@ reflect swapV @-}
swapV :: Ix n -> Ix n -> Vec (Suc n) e -> Vec (Suc n) e
swapV i j v =
  let xi = readV i v in
  let xj = readV i v in
  writeV xj i (writeV xi j v)

-- Permutation

-- TODO: not sure if this is right...
{-@
type Permutation V1 V2 = EqL (Int -> Int) {count V1} {count V2}
@-}
type Permutation = EqL (Int -> Int)

-- {-@ reflect permutationFor @-}
-- permutationFor :: Vec n Int -> Vec n Int -> Int -> Bool
-- permutationFor v1 v2 x = count v1 x == count v2 x

{-@ reflect count @-}
{-@
count :: Vec n Int -> Int -> {c:Int | 0 <= c}
@-}
count :: Vec n Int -> Int -> Int
count Nil y = 0
count (Cons x xs) y = if x == y then add1 (count xs y) else count xs y

-- {-@ reflect permutation_reflexive @-} -- can't reflect because can't reflect `reflexivity`
{-@
permutation_reflexive :: v:Vec n Int -> Permutation {v} {v}
@-}
permutation_reflexive :: Vec n Int -> Permutation
permutation_reflexive v = undefined -- extensionality (count v) (count v) (permutation_reflexive_aux v)

-- {-@ reflect permutation_reflexive_aux @-} -- can't reflect because can't reflect `reflexivity`
{-@
permutation_reflexive_aux :: v:Vec n Int -> Int -> EqL Int {count v} {count v}
@-}
permutation_reflexive_aux :: Vec n Int -> Int -> EqL Int
permutation_reflexive_aux v x = reflexivity (count v x)

{-@
permutation_symmetric :: v1:Vec n Int -> v2:Vec n Int -> Permutation {v1} {v2} -> Permutation {v2} {v1}
@-}
permutation_symmetric :: Vec n Int -> Vec n Int -> Permutation -> Permutation
permutation_symmetric v1 v2 perm12 =
  extensionality (count v2) (count v1) (\x ->
    inject (count v2 x) (count v2 x)
      (extract (count v1 x) (count v2 x)
        (contractability (count v1) (count v2) perm12 x)))

{-@
permutation_transitive :: v1:Vec n Int -> v2:Vec n Int -> v3:Vec n Int -> Permutation {v1} {v2} -> Permutation {v2} {v3} -> Permutation {v1} {v3}
@-}
permutation_transitive :: Vec n Int -> Vec n Int -> Vec n Int -> Permutation -> Permutation -> Permutation
permutation_transitive v1 v2 v3 perm12 perm23 = undefined -- TODO

{-@
permutation_swapV :: i:Ix n -> j:Ix n -> v:Vec (Suc n) Int -> Permutation {v} {swapV i j v}
@-}
permutation_swapV :: Ix n -> Ix n -> Vec (Suc n) Int -> Permutation
permutation_swapV = undefined


-- State

-- {-@
-- type State s1 s2 a = s1 -> (a, s2)
-- @-}
type State s1 s2 a = s1 -> (a, s2)

{-@ reflect returnS @-}
returnS :: a -> State s s a
returnS a s = (a, s)

{-@ reflect bindS @-}
bindS :: State s1 s2 a -> (a -> State s2 s3 b) -> State s1 s3 b
bindS m k s1 =  let (a, s2) = m s1 in k a s2

{-@ reflect constant @-}
constant :: a -> b -> a
constant a _ = a

{-@ reflect seqS @-}
seqS :: State s1 s2 a -> State s2 s3 b -> State s1 s3 b
seqS m1 m2 = bindS m1 (constant m2)

{-@ reflect getS @-}
getS :: State s s s
getS s = (s, s)

{-@ reflect putS @-}
putS :: s2 -> State s1 s2 Unit 
putS s2 _ = (unit, s2)

-- Array

-- {-@
-- type Permutation V1 V2 = EqL (Int -> Int) {count V1} {count V2}
-- @-}
-- type Permutation = EqL (Int -> Int)

-- invariants:
-- - permutation
{-@
type Array n a = v1:Vec n Int -> (a, v2::Vec n Int, EqL (Int -> Int) {count v1} {count v2})
@-}
type Array n a = Vec n Int -> (a, Vec n Int, Permutation)

-- {-@ reflect readA @-} -- can't reflect because can't reflect `reflexivity`
{-@
readA :: Ix n -> v1:Vec (Suc n) Int -> (Int, v2::Vec (Suc n) Int, pr:((Int -> Int) -> Bool) -> {pr (count v1) == pr (count v2)})
@-}
-- EqL (Int -> Int) {count v1} {count v2})
readA :: Ix n -> Array (Suc n) Int
readA i v = (readV i v, v, permutation_reflexive v)

-- -- don't allow normal writes, since not necessarily a permutation
-- -- {-@
-- -- writeA :: Int -> Ix n -> Array (Suc n) Int
-- -- @-}
-- -- writeA :: Int -> Ix n -> Array (Suc n) Int
-- -- writeA x i v = (unit, writeV x i v, )


-- -- {-@
-- -- swapA :: Ix n -> Ix n -> Array (Suc n) Unit
-- -- @-}
-- {-@
-- swapA :: Ix n -> Ix n -> v1:Vec (Suc n) Int -> (Int, v2::Vec (Suc n) Int, {_:EqualProp (Int -> Int) | eqp (count v1) (count v2)})
-- @-}
-- swapA :: Ix n -> Ix n -> Array (Suc n) Unit
-- swapA i j v = (unit, swapV i j v, permutation_swapV i j v)

-- swapA_permutation :: i:Ix n -> j:Ix n -> Array (Suc n) Unit {p} {Permutation _}
-- swapA_permutation ... = swapA i j
