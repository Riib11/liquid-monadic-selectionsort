{-# LANGUAGE GADTs, DataKinds, ExplicitForAll #-}
{-@ LIQUID "--no-totality" @-}

module QuickSort.MonadicV2 where

import Proof
import Relation.Equality.Prop
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
type Permutation n V1 V2 = EqP (x:Int -> {permutationFor V1 V2 x})
@-}
type Permutation n = EqP (Int -> Vec n Int -> Proof)

{-@ reflect permutationFor @-}
permutationFor :: Vec (Suc n) Int -> Vec (Suc n) Int -> Int -> Bool
permutationFor v1 v2 x = count v1 x == count v2 x

{-@ reflect count @-}
{-@
count :: Vec n Int -> Int -> {c:Int | 0 <= c}
@-}
count :: Vec n Int -> Int -> Int
count Nil y = 0
count (Cons x xs) y = if x == y then add1 (count xs y) else count xs y

-- State

{-@
type State s1 s2 a = s1 -> (a, s2)
@-}
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

-- TODO: make the proofs extrinsic. don't do intrinsically, no refinements on state input/output. first try without, maybe keep different type variables  just in case tries to constrain same refinements

-- invariants:
-- - permutation
{-@
type Array n a = v1:Vec (Suc n) Int -> (a, v2::Vec (Suc n) Int, Permutation (Suc n) {v1} {v2})
@-}
type Array n a = Vec (Suc n) Int -> (a, Vec (Suc n) Int, Permutation (Suc n))

{-@ reflect readA @-}
readA :: Ix n -> Array (Suc n) Int
readA i v = read

-- Array [OLD]

-- {-@
type Array n e a P1 P2 = State ({l:Vec n e | P1 l}) ({l:Vec n e | P2 l}) a
@-}
type Array n e a = State (Vec n e) (Vec n e) a

-- {-@
-- type PredA n e = Vec n e -> Proof
-- @-}
-- type PredA n e = Vec n e -> Proof

{-@ reflect readA @-}
{-@
readA :: p:PredA (Suc n) e -> Ix n -> Array (Suc n) e e {p} {p}
@-}
readA :: PredA (Suc n) e -> Ix n -> Array (Suc n) e e
readA _ i v = (readV i v, v)

{-@
writeA ::
  p1:PredA (Suc n) e -> p2:PredA (Suc n) e ->
  x:e -> i:Ix n ->
  (v:{Vec (Suc n) e | p1 v} -> {p2 (writeV x i v)}) ->
  Array (Suc n) e Unit {p1} {p2}
@-}
writeA ::
  PredA (Suc n) e -> PredA (Suc n) e ->
  e -> Ix n ->
  (Vec (Suc n) e -> Proof) ->
  Array (Suc n) e Unit
writeA _ _ x i hyp v = (unit, writeV x i (v `by` hyp v))

-- -- TODO: Implement in terms of `readA` and `writeA` rather than operating directly on the underlying list. But, this doesn't make any different extrinsically.
{-@
swapA ::
  p1:PredA (Suc n) e -> p2:PredA (Suc n) e ->
  i:Ix n -> j:Ix n ->
  (v:{Vec (Suc n) e | p1 v} -> {p2 (swapV i j v)}) ->
  -- Array (Suc n) e Unit {p1} {p2}
  -- Vec (Suc n) e -> (Unit, Vec (Suc n) e)
@-}
swapA ::
  PredA (Suc n) e -> PredA (Suc n) e ->
  Ix n -> Ix n ->
  (Vec (Suc n) e -> Proof) ->
  Array (Suc n) e Unit
swapA p1 p2 i j hyp v = (unit, swapV i j (v `by` hyp v))

-- -- prove that `swapA` is a permutation

-- -- -- p:PredA (Suc n) e ->
-- {-@
-- swapA_permutation ::
--   i:Ix n -> j:Ix n ->
--   Array (Suc n) Int Unit {\_ -> unit} {\_ -> }
-- @-}

swapA_permutation :: i:Ix n -> j:Ix n -> v:Vec (Suc n) Int -> Permutation {v} {swapA i j v}