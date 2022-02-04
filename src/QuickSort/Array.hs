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

{-@ reflect readA_readA_lhs @-}
readA_readA_lhs :: (m El -> (El -> m a) -> m a) -> (Int -> m El) -> Int -> (El -> El -> m a) -> m a
readA_readA_lhs b r i f = b (r i) (readA_readA_lhs_aux1 b r i f)

{-@ reflect readA_readA_lhs_aux1 @-}
readA_readA_lhs_aux1 :: (m El -> (El -> m a) -> m a) -> (Int -> m El) -> Int -> (El -> El -> m a) -> El -> m a
readA_readA_lhs_aux1 b r i f x = b (r i) (readA_readA_lhs_aux2 f x)

{-@ reflect readA_readA_lhs_aux2 @-}
readA_readA_lhs_aux2 :: (El -> El -> m a) -> El -> El -> m a
readA_readA_lhs_aux2 f x y = f x y

{-@ reflect readA_readA_rhs @-}
readA_readA_rhs :: (m El -> (El -> m a) -> m a) -> (Int -> m El) -> Int -> (El -> El -> m a) -> m a
readA_readA_rhs b r i f = b (r i) (readA_readA_rhs_aux1 f)

{-@ reflect readA_readA_rhs_aux1 @-}
readA_readA_rhs_aux1 :: (El -> El -> m a) -> El -> m a
readA_readA_rhs_aux1 f x = f x x

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
readA_readA :: forall a. i:Int -> f:(El -> El -> m a) ->
  Equal (m a)
    {readA_readA_lhs bindA readA i f}
    {readA_readA_rhs bindA readA i f}
-}

{-@ reflect swapA_readA_i_aux @-}
swapA_readA_i_aux ::
  (El -> m El) ->
  (m El -> (El -> m El) -> m El) ->
  (m Unit -> (Unit -> m El) -> m El) ->
  (Int -> m El) ->
  (Int -> Int -> m Unit) ->
  Int ->
  Int ->
  m El
swapA_readA_i_aux p b1 b2 r s i j =
  b1 (r j) (swapA_readA_i_aux_aux p b2 s i j)

{-@ reflect swapA_readA_i_aux_aux @-}
swapA_readA_i_aux_aux ::
  (El -> m El) ->
  (m Unit -> (Unit -> m El) -> m El) ->
  (Int -> Int -> m Unit) ->
  Int ->
  Int ->
  El ->
  m El
swapA_readA_i_aux_aux p b s i j x =
  seqA_proto b (s i j) (p x)

{-@
data Array m = Array
  { pureA :: forall a. a -> m a,
    bindA :: forall a b. m a -> (a -> m b) -> m b,

    pureA_bindA :: forall a b. a:a -> k:(a -> m b) ->
      Equal (m b) {bindA (pureA a) k} {k a},
    bindA_pureA :: forall a. m:m a ->
      Equal (m a) {bindA m pureA} {m},
    bindA_bindA :: forall a b c. m:m a -> k1:(a -> m b) -> k2:(b -> m c) ->
      Equal (m c)
        {bindA (bindA m k1) k2}
        {bindA m (kleisliA_proto bindA k1 k2)},

    lengthA :: Int,
    positive_lengthA :: {0 <= lengthA},

    readA :: {i:Int | inBounds lengthA i} -> m El,
    swapA :: {i:Int | inBounds lengthA i} -> {j:Int | inBounds lengthA j} -> m Unit,

    swapA_readA_i :: {i:Int | inBounds lengthA i} -> {j:Int | inBounds lengthA j} ->
      Equal (m El)
        {seqA_proto bindA (swapA i j) (readA i)}
        {swapA_readA_i_aux pureA bindA bindA readA swapA i j},

    readA_readA :: forall a. i:Int -> f:(El -> El -> m a) ->
      Equal (m a)
        {readA_readA_lhs bindA readA i f}
        {readA_readA_rhs bindA readA i f}
  }
@-}
data Array m = Array
  { -- monad fields
    pureA :: forall a. a -> m a,
    bindA :: forall a b. m a -> (a -> m b) -> m b,
    -- monad laws
    pureA_bindA :: forall a b. a -> (a -> m b) -> Equal (m b),
    bindA_pureA :: forall a. m a -> Equal (m a),
    bindA_bindA :: forall a b c. m a -> (a -> m b) -> (b -> m c) -> Equal (m c),
    -- array length
    lengthA :: Int,
    positive_lengthA :: Proof,
    -- array fields
    readA :: Int -> m El,
    swapA :: Int -> Int -> m Unit,
    -- array laws
    swapA_readA_i :: Int -> Int -> Equal (m El),
    -- readSwap_j :: Int -> Int -> Equal (m Unit),

    -- readWriteA :: Int -> Equal (m Unit),
    -- writeReadA :: Int -> El -> Equal (m El),
    -- writeWriteA :: Int -> El -> El -> Equal (m Unit),

    readA_readA :: forall a. Int -> (El -> El -> m a) -> Equal (m a)
  }

-- assumption
-- not sure how to prove these, but are definitely true

{-@
seqA_readA :: iA:Array m -> i:{Int | inBoundsA iA i} -> m:m a ->
  Equal (m a)
    {seqA iA (readA iA i) m}
    {m}
@-}
seqA_readA :: Array m -> Int -> m a -> Equal (m a)
seqA_readA iA i m = undefined -- ! ASSUMPTION

-- synthetic monad functions

{-@ inline fmapA @-}
fmapA :: forall m a b. Array m -> (a -> b) -> m a -> m b
fmapA iA f ma = bindA iA ma (pureA iA . f)

{-@ inline seqA @-}
seqA :: forall m a b. Array m -> m a -> m b -> m b
seqA iA ma mb = bindA iA ma (constant mb)

{-@ inline kleisliA @-}
kleisliA :: forall m a b c. Array m -> (a -> m b) -> (b -> m c) -> (a -> m c)
kleisliA iA k1 k2 a = bindA iA (k1 a) k2

-- inboundsA
-- property that an index is inbounds of an array

{-@ inline inBoundsA @-}
inBoundsA :: Array m -> Int -> Bool
inBoundsA iA i = 0 <= i && i < lengthA iA

-- equalities
-- convenient equalities over Array

{-@
congruency_bindA_m ::
  forall m a b.
  iA:Array m ->
  m1:m a -> m2:m a ->
  k:(a -> m b) ->
  Equal (m a) {m1} {m2} ->
  Equal (m b) {bindA iA m1 k} {bindA iA m2 k}
@-}
congruency_bindA_m ::
  forall m a b.
  Array m ->
  m a ->
  m a ->
  (a -> m b) ->
  Equal (m a) ->
  Equal (m b)
congruency_bindA_m iA m1 m2 k eq_m1_m2 =
  (reframe (bindA iA m1) (bindA iA m2) k)
    (congruency (bindA iA) m1 m2 eq_m1_m2)

{-@
congruency_bindA_k ::
  forall m a b.
  iA:Array m ->
  m:m a ->
  k1:(a -> m b) -> k2:(a -> m b) ->
  Equal (a -> m b) {k1} {k2} ->
  Equal (m b) {bindA iA m k1} {bindA iA m k2}
@-}
congruency_bindA_k ::
  forall m a b.
  Array m ->
  m a ->
  (a -> m b) ->
  (a -> m b) ->
  Equal (a -> m b) ->
  Equal (m b)
congruency_bindA_k iA m k1 k2 eq_k1_k2 =
  congruency (bindA iA m) k1 k2 eq_k1_k2

{-@
bindA_pureA_eq_seqA_pureA_unit ::
  iA:Array m ->
  m:m Unit ->
  Equal (m Unit)
    {bindA iA m (pureA iA)}
    {seqA iA m (pureA iA unit)}
@-}
bindA_pureA_eq_seqA_pureA_unit :: Array m -> m Unit -> Equal (m Unit)
bindA_pureA_eq_seqA_pureA_unit iA m =
  (congruency_bindA_k iA m (pureA iA) (constant (pureA iA unit)))
    ( (extensionality (pureA iA) (constant (pureA iA unit)))
        (bindA_pureA_eq_seqA_pureA_unit_aux iA)
    )

{-@ automatic-instances bindA_pureA_eq_seqA_pureA_unit_aux @-}
{-@
bindA_pureA_eq_seqA_pureA_unit_aux ::
  iA:Array m -> x:Unit ->
  Equal (m Unit)
    {pureA iA x}
    {constant (pureA iA unit) x}
@-}
bindA_pureA_eq_seqA_pureA_unit_aux :: Array m -> Unit -> Equal (m Unit)
bindA_pureA_eq_seqA_pureA_unit_aux iA () = reflexivity (pureA iA ())

-- permutationA
-- a permutationA is a sequence of swaps

{-@ reflect permutationA @-}
{-@
permutationA :: iA:Array m -> [({i:Int | inBoundsA iA i}, {j:Int | inBoundsA iA j})] -> m Unit
@-}
permutationA :: Array m -> [(Int, Int)] -> m Unit
permutationA iA [] = pureA iA unit
permutationA iA ((i, j) : ijs) = seqA iA (swapA iA i j) (permutationA iA ijs)

{-@
type Permutation m A M IJ = Equal (m Unit) {seqA A M (pureA A unit)} {permutationA A IJ}
@-}
type Permutation m = Equal (m Unit)

{-@ automatic-instances permutationA_swapA @-}
{-@
permutationA_swapA :: iA:Array m -> i:{Int | inBoundsA iA i} -> j:{Int | inBoundsA iA j} ->
  Permutation m {iA} {swapA iA i j} {[(i, j)]}
@-}
permutationA_swapA :: Array m -> Int -> Int -> Permutation m
permutationA_swapA iA i j = reflexivity (seqA iA (swapA iA i j) (pureA iA unit))

{-@ automatic-instances permutationA_readA @-}
{-@
permutationA_readA :: iA:Array m -> i:{Int | inBoundsA iA i} ->
  Permutation m {iA} {readA iA i} {[]}
@-}
permutationA_readA :: Array m -> Int -> Permutation m
permutationA_readA iA i =
  seqA_readA iA i (pureA iA unit)
