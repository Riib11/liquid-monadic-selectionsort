{-# LANGUAGE GADTs, DataKinds, ExplicitForAll #-}
{-@ LIQUID "--no-totality" @-}

module QuickSort.MonadicV4 where

import Proof
-- import Relation.Equality.Prop
import Relation.Equality.Leibniz
import Refined.Data.Unit
import Refined.Data.Int
-- import Refined.Data.Vec

-- data Nat

{-@
data Nat = Zero | Suc Nat
@-}
data Nat = Zero | Suc Nat
  deriving (Show)

-- data SNat

data SNat :: Nat -> * where
  SZero :: SNat Zero
  SSuc :: SNat n -> SNat (Suc n)

-- data Ix

data Ix :: Nat -> * where
  IxZero :: Ix (Suc n)
  IxSuc :: Ix n -> Ix (Suc n)

instance Eq (Ix n) where
  IxZero == IxZero
  IxSuc i == Ix Suc j = i == j

-- leIx

{-@ reflect leIx @-}
leIx :: Ix n -> Ix n -> Bool
leIx IxZero _ = True
leIx (IxSuc i) IxZero = False
leIx (IxSuc i) (IxSuc j) = leIx i j

-- ! no no no no no no....
-- -- rangeIx

-- rangeIx :: SNat n -> [Ix n]
-- rangeIx 

-- type Vec

type Vec n a = Ix n -> a

-- Permuted

-- forall x y, f x = f y => x = y
-- {-@
-- Injection a b = x:a -> (y::b, EqL (a -> Bool) )
-- @-}

-- isInjectionL f v1 v2 = if f v1 f v2 then v1 == v2 else 

-- {-@
-- IsInjection n F = EqL (Vec n Int -> Vec n Int -> Bool) {isInjectionL} {isInjectionR}
-- @-}
-- IsInjection n = EqL (Vec n Int -> Ix n -> Ix n -> Bool)

-- exists bijection between V1 and V2
{-@
type Permuted V1 V2 = EqL (Int -> Int) {count V1} {count V2}
@-}
type Permuted = EqL (Int -> Int)

-- no, because don't want to range over indices
-- -- count

-- count :: Vec n Int -> Int -> Int
-- count v x = foldV (count_aux x) 0 v

-- count_aux :: Int -> Int -> Int -> Ix n -> Int
-- count_aux x c y i = if x == y then add1 c else c

-- Sorted

{-@ reflect sortedAt @-}
sortedAt :: Vec n Int -> Ix n -> Ix n -> Bool
sortedAt v i j = if leIx i j then le (v i) (v j) else True

{-@
type Sorted n V = EqL (Ix n -> Ix n -> Bool) {sortedAt} {constant2r True}
@-}
type Sorted = EqL (Int -> Int -> Bool)

-- -- {-@ reflect permutationFor @-}
-- -- permutationFor :: Vec n Int -> Vec n Int -> Int -> Bool
-- -- permutationFor v1 v2 x = count v1 x == count v2 x

-- {-@ reflect count @-}
-- {-@
-- count :: Vec n Int -> Int -> {c:Int | 0 <= c}
-- @-}
-- count :: Vec n Int -> Int -> Int
-- count Nil y = 0
-- count (Cons x xs) y = if x == y then add1 (count xs y) else count xs y

-- -- {-@ reflect permutation_reflexive @-} -- can't reflect because can't reflect `reflexivity`
-- {-@
-- permutation_reflexive :: v:Vec n Int -> Permuted {v} {v}
-- @-}
-- permutation_reflexive :: Vec n Int -> Permuted
-- permutation_reflexive v = undefined -- extensionality (count v) (count v) (permutation_reflexive_aux v)

-- -- {-@ reflect permutation_reflexive_aux @-} -- can't reflect because can't reflect `reflexivity`
-- {-@
-- permutation_reflexive_aux :: v:Vec n Int -> Int -> EqL Int {count v} {count v}
-- @-}
-- permutation_reflexive_aux :: Vec n Int -> Int -> EqL Int
-- permutation_reflexive_aux v x = reflexivity (count v x)

-- {-@
-- permutation_symmetric :: v1:Vec n Int -> v2:Vec n Int -> Permuted {v1} {v2} -> Permuted {v2} {v1}
-- @-}
-- permutation_symmetric :: Vec n Int -> Vec n Int -> Permuted -> Permuted
-- permutation_symmetric v1 v2 perm12 =
--   extensionality (count v2) (count v1) (\x ->
--     inject (count v2 x) (count v2 x)
--       (extract (count v1 x) (count v2 x)
--         (contractability (count v1) (count v2) perm12 x)))

-- {-@
-- permutation_transitive :: v1:Vec n Int -> v2:Vec n Int -> v3:Vec n Int -> Permuted {v1} {v2} -> Permuted {v2} {v3} -> Permuted {v1} {v3}
-- @-}
-- permutation_transitive :: Vec n Int -> Vec n Int -> Vec n Int -> Permuted -> Permuted -> Permuted
-- permutation_transitive v1 v2 v3 perm12 perm23 = undefined -- TODO

-- {-@
-- permutation_swapV :: i:Ix n -> j:Ix n -> v:Vec (Suc n) Int -> Permuted {v} {swapV i j v}
-- @-}
-- permutation_swapV :: Ix n -> Ix n -> Vec (Suc n) Int -> Permuted
-- permutation_swapV = undefined


-- -- State

-- -- {-@
-- -- type State s1 s2 a = s1 -> (a, s2)
-- -- @-}
-- type State s1 s2 a = s1 -> (a, s2)

-- {-@ reflect returnS @-}
-- returnS :: a -> State s s a
-- returnS a s = (a, s)

-- {-@ reflect bindS @-}
-- bindS :: State s1 s2 a -> (a -> State s2 s3 b) -> State s1 s3 b
-- bindS m k s1 =  let (a, s2) = m s1 in k a s2

-- {-@ reflect seqS @-}
-- seqS :: State s1 s2 a -> State s2 s3 b -> State s1 s3 b
-- seqS m1 m2 = bindS m1 (constant m2)

-- {-@ reflect getS @-}
-- getS :: State s s s
-- getS s = (s, s)

-- {-@ reflect putS @-}
-- putS :: s2 -> State s1 s2 Unit 
-- putS s2 _ = (unit, s2)

-- -- Array

-- -- {-@
-- -- type Permuted V1 V2 = EqL (Int -> Int) {count V1} {count V2}
-- -- @-}
-- -- type Permuted = EqL (Int -> Int)

-- -- invariants:
-- -- - permutation
-- {-@
-- type Array n a = v1:Vec n Int -> (a, v2::Vec n Int, EqL (Int -> Int) {count v1} {count v2})
-- @-}
-- type Array n a = Vec n Int -> (a, Vec n Int, Permuted)

-- -- {-@ reflect readA @-} -- can't reflect because can't reflect `reflexivity`
-- {-@
-- readA :: Ix n -> v1:Vec (Suc n) Int -> (Int, v2::Vec (Suc n) Int, pr:((Int -> Int) -> Bool) -> {pr (count v1) == pr (count v2)})
-- @-}
-- -- EqL (Int -> Int) {count v1} {count v2})
-- readA :: Ix n -> Array (Suc n) Int
-- readA i v = (readV i v, v, permutation_reflexive v)

-- -- -- don't allow normal writes, since not necessarily a permutation
-- -- -- {-@
-- -- -- writeA :: Int -> Ix n -> Array (Suc n) Int
-- -- -- @-}
-- -- -- writeA :: Int -> Ix n -> Array (Suc n) Int
-- -- -- writeA x i v = (unit, writeV x i v, )


-- -- -- {-@
-- -- -- swapA :: Ix n -> Ix n -> Array (Suc n) Unit
-- -- -- @-}
-- -- {-@
-- -- swapA :: Ix n -> Ix n -> v1:Vec (Suc n) Int -> (Int, v2::Vec (Suc n) Int, {_:EqualProp (Int -> Int) | eqp (count v1) (count v2)})
-- -- @-}
-- -- swapA :: Ix n -> Ix n -> Array (Suc n) Unit
-- -- swapA i j v = (unit, swapV i j v, permutation_swapV i j v)

-- -- swapA_permutation :: i:Ix n -> j:Ix n -> Array (Suc n) Unit {p} {Permuted _}
-- -- swapA_permutation ... = swapA i j
