{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--short-names" @-}

module QuickSort.Array where

import Proof
import Refined.Data.Int
import Refined.Data.Unit
import Refined.Function
import Relation.Equality.Leibniz

type El = Int

{-@ inline inBounds @-}
inBounds :: Int -> Int -> Bool
inBounds l i = 0 <= i && i < l

{-@ reflect kleisliA_proto @-}
kleisliA_proto :: (m b -> (b -> m c) -> m c) -> (a -> m b) -> (b -> m c) -> (a -> m c)
kleisliA_proto b k1 k2 x = b (k1 x) k2

{-@ reflect seqA_proto @-}
seqA_proto :: (m a -> (a -> m b) -> m b) -> m a -> m b -> m b
seqA_proto b m1 m2 = b m1 (constant m2)

{-@ reflect readReadA_lhs @-}
readReadA_lhs :: (m El -> (El -> m a) -> m a) -> (Int -> m El) -> Int -> (El -> El -> m a) -> m a
readReadA_lhs b r i f = b (r i) (readReadA_lhs_aux1 b r i f)

{-@ reflect readReadA_lhs_aux1 @-}
readReadA_lhs_aux1 :: (m El -> (El -> m a) -> m a) -> (Int -> m El) -> Int -> (El -> El -> m a) -> El -> m a
readReadA_lhs_aux1 b r i f x = b (r i) (readReadA_lhs_aux2 f x)

{-@ reflect readReadA_lhs_aux2 @-}
readReadA_lhs_aux2 :: (El -> El -> m a) -> El -> El -> m a
readReadA_lhs_aux2 f x y = f x y

{-@ reflect readReadA_rhs @-}
readReadA_rhs :: (m El -> (El -> m a) -> m a) -> (Int -> m El) -> Int -> (El -> El -> m a) -> m a
readReadA_rhs b r i f = b (r i) (readReadA_rhs_aux1 f)

{-@ reflect readReadA_rhs_aux1 @-}
readReadA_rhs_aux1 :: (El -> El -> m a) -> El -> m a
readReadA_rhs_aux1 f x = f x x

{-
readWriteA :: i:Int ->
  Equal (m Unit)
    {bindA (readA i) (writeA i)}
    {pureA unit},
writeReadA :: i:Int -> x:El ->
  Equal (m El)
    {seqA_proto bindA (writeA i x) (readA i)}
    {seqA_proto bindA (writeA i x) (pureA x)},
writeWriteA :: i:Int -> x:El -> y:El ->
  Equal (m Unit)
    {seqA_proto bindA (writeA i x) (writeA i y)}
    {writeA i y},
readReadA :: forall a. i:Int -> f:(El -> El -> m a) ->
  Equal (m a)
    {readReadA_lhs bindA readA i f}
    {readReadA_rhs bindA readA i f}
-}

{-@ reflect readSwapA_i_aux @-}
readSwapA_i_aux ::
  (El -> m El) ->
  (m El -> (El -> m El) -> m El) ->
  (m Unit -> (Unit -> m El) -> m El) ->
  (Int -> m El) ->
  (Int -> Int -> m Unit) ->
  Int ->
  Int ->
  m El
readSwapA_i_aux p b1 b2 r s i j =
  b1 (r j) (readSwapA_i_aux_aux p b2 s i j)

{-@ reflect readSwapA_i_aux_aux @-}
readSwapA_i_aux_aux ::
  (El -> m El) ->
  (m Unit -> (Unit -> m El) -> m El) ->
  (Int -> Int -> m Unit) ->
  Int ->
  Int ->
  El ->
  m El
readSwapA_i_aux_aux p b s i j x =
  seqA_proto b (s i j) (p x)

{-@
data Array m = Array
  { pureA :: forall a. a -> m a,
    bindA :: forall a b. m a -> (a -> m b) -> m b,

    pureBindA :: forall a b. a:a -> k:(a -> m b) ->
      Equal (m b) {bindA (pureA a) k} {k a},
    bindPureA :: forall a. m:m a ->
      Equal (m a) {bindA m pureA} {m},
    assocA :: forall a b c. m:m a -> k1:(a -> m b) -> k2:(b -> m c) ->
      Equal (m c)
        {bindA (bindA m k1) k2}
        {bindA m (kleisliA_proto bindA k1 k2)},

    lengthA :: Int,
    positive_lengthA :: {0 <= lengthA},

    readA :: {i:Int | inBounds lengthA i} -> m El,
    swapA :: {i:Int | inBounds lengthA i} -> {j:Int | inBounds lengthA j} -> m Unit,

    readSwapA_i :: {i:Int | inBounds lengthA i} -> {j:Int | inBounds lengthA j} ->
      Equal (m El)
        {seqA_proto bindA (swapA i j) (readA i)}
        {readSwapA_i_aux pureA bindA bindA readA swapA i j},
    readReadA :: forall a. i:Int -> f:(El -> El -> m a) ->
      Equal (m a)
        {readReadA_lhs bindA readA i f}
        {readReadA_rhs bindA readA i f}
  }
@-}
{-

-}
data Array m = Array
  { -- monad fields
    pureA :: forall a. a -> m a,
    bindA :: forall a b. m a -> (a -> m b) -> m b,
    -- monad laws
    pureBindA :: forall a b. a -> (a -> m b) -> Equal (m b),
    bindPureA :: forall a. m a -> Equal (m a),
    assocA :: forall a b c. m a -> (a -> m b) -> (b -> m c) -> Equal (m c),
    -- array length
    lengthA :: Int,
    positive_lengthA :: Proof,
    -- array fields
    readA :: Int -> m El,
    swapA :: Int -> Int -> m Unit,
    -- array laws
    readSwapA_i :: Int -> Int -> Equal (m El),
    -- readSwap_j :: Int -> Int -> Equal (m Unit),

    -- readWriteA :: Int -> Equal (m Unit),
    -- writeReadA :: Int -> El -> Equal (m El),
    -- writeWriteA :: Int -> El -> El -> Equal (m Unit),

    readReadA :: forall a. Int -> (El -> El -> m a) -> Equal (m a)
  }

-- synthetic monad functions

{-@ inline fmapA @-}
fmapA :: forall m a b. Array m -> (a -> b) -> m a -> m b
fmapA _A f ma = bindA _A ma (pureA _A . f)

{-@ inline seqA @-}
seqA :: forall m a b. Array m -> m a -> m b -> m b
seqA _A ma mb = bindA _A ma (constant mb)

{-@ inline kleisliA @-}
kleisliA :: forall m a b c. Array m -> (a -> m b) -> (b -> m c) -> (a -> m c)
kleisliA _A k1 k2 a = bindA _A (k1 a) k2

-- inboundsA
-- property that an index is inbounds of an array

{-@ inline inBoundsA @-}
inBoundsA :: Array m -> Int -> Bool
inBoundsA _A i = 0 <= i && i < lengthA _A

-- permutationA
-- a permutationA is a sequence of swaps

{-@ reflect permutationA @-}
{-@
permutationA :: _A:Array m -> [({i:Int | inBoundsA _A i}, {j:Int | inBoundsA _A j})] -> m Unit
@-}
permutationA :: Array m -> [(Int, Int)] -> m Unit
permutationA _A [] = pureA _A unit
permutationA _A ((i, j) : ijs) = seqA _A (swapA _A i j) (permutationA _A ijs)

{-@
type Permutation m A M IJ = Equal (m Unit) {M} {permutationA A IJ}
@-}
type Permutation m = Equal (m Unit)

{-@ automatic-instances permutationA_swapA @-}
{-@
permutationA_swapA :: _A:Array m -> i:{Int | inBoundsA _A i} -> j:{Int | inBoundsA _A j} ->
  Permutation m {_A} {swapA _A i j} {[(i, j)]}
@-}
permutationA_swapA :: Array m -> Int -> Int -> Permutation m
permutationA_swapA _A i j =
  transitivity
    (swapA _A i j)
    (bindA _A (swapA _A i j) (pureA _A))
    (permutationA _A [(i, j)])
    ( symmetry
        (bindA _A (swapA _A i j) (pureA _A))
        (swapA _A i j)
        (bindPureA _A (swapA _A i j))
    )
    (bindA_pureA_eq_seqA_pureA_unit _A (swapA _A i j))

{-@
bindA_pureA_eq_seqA_pureA_unit ::
  _A:Array m ->
  m:m Unit ->
  Equal (m Unit)
    {bindA _A m (pureA _A)}
    {seqA _A m (pureA _A unit)}
@-}
bindA_pureA_eq_seqA_pureA_unit :: Array m -> m Unit -> Equal (m Unit)
bindA_pureA_eq_seqA_pureA_unit = undefined
