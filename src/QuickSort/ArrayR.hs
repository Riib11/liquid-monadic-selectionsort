{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--notermination" @-}

module QuickSort.ArrayR where

-- Function

{-@ reflect constant @-}
constant :: a -> b -> a
constant a _ = a

-- Proof

{-@
type Proof = ()
@-}
type Proof = ()

{-@ inline unreachable @-}
-- {-@ unreachable :: {v : Proof | False} @-}
unreachable :: Proof
unreachable = ()

{-@ inline trivial @-}
trivial :: Proof
trivial = ()

{-@ inline refinement @-}
refinement :: a -> Proof
refinement _ = trivial

{-@ inline by @-}
by :: a -> b -> a
by x _ = x

{-@ inline by @-}
by_refinement :: a -> b -> a
by_refinement x y = x `by` refinement y

{-@
assume :: b:Bool -> {b}
@-}
assume :: Bool -> Proof
assume b = undefined

{-@
assert :: {b:Bool | b} -> {b}
@-}
assert :: Bool -> Proof
assert b = trivial

{-@ inline begin @-}
begin :: a -> Proof
begin _ = trivial

infixl 3 ===

{-@ infixl 3 === @-}
{-@ inline === @-}
{-@
(===) :: x:a -> y:{a | y = x} -> z:{a | z = x && z = y}
@-}
(===) :: a -> a -> a
x === y = y

-- Refined.Data.Unit

{-@
type Unit = ()
@-}
type Unit = ()

{-@ inline unit @-}
unit :: Unit
unit = ()

-- Relation.Equality.Leibniz

{-@
type Equal a X Y = prop:(a -> Bool) -> {prop X = prop Y}
@-}
type Equal a = (a -> Bool) -> Proof

{-@
type NotEqual a X Y = Equal a X Y -> {False}
@-}
type NotEqual a = Equal a -> Proof

{-@
reflexivity :: x:a -> Equal a {x} {x}
@-}
reflexivity :: a -> Equal a
reflexivity a pr = trivial

{-@
symmetry :: x:a -> y:a -> Equal a {x} {y} -> Equal a {y} {x}
@-}
symmetry :: a -> a -> Equal a -> Equal a
symmetry x y eq_x_y = undefined

{-@
transitivity :: x:a -> y:a -> z:a -> Equal a {x} {y} -> Equal a {y} {z} -> Equal a {x} {z}
@-}
transitivity :: a -> a -> a -> Equal a -> Equal a -> Equal a
transitivity x y z eq_x_y eq_y_z = undefined

{-@
congruency :: f:(a -> b) -> x:a -> y:a -> Equal a {x} {y} -> Equal b {f x} {f y}
@-}
congruency :: (a -> b) -> a -> a -> Equal a -> Equal b
congruency f x y eq_x_y = undefined

{-@
assume extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> Equal b {f x} {g x}) -> Equal (a -> b) {f} {g}
@-}
extensionality :: (a -> b) -> (a -> b) -> (a -> Equal b) -> Equal (a -> b)
extensionality f g eq pr = trivial

{-@
assume contractability :: f:(a -> b) -> g:(a -> b) -> x:a -> Equal (a -> b) {f} {g} -> Equal b {f x} {g x}
@-}
contractability :: (a -> b) -> (a -> b) -> a -> Equal (a -> b) -> Equal b
contractability f g eq a pr = trivial

{-@
inject :: forall a. x:a -> y:{y:a | x = y} -> Equal a {x} {y}
@-}
inject :: forall a. a -> a -> Equal a
inject x y = reflexivity x

{-@
assume extract :: x:a -> y:a -> Equal a {x} {y} -> {x = y}
@-}
extract :: a -> a -> Equal a -> Proof
extract x y eq = trivial

{-@
assumeEqual :: x:a -> y:a -> Equal a {x} {y}
@-}
assumeEqual :: a -> a -> Equal a
assumeEqual _ _ = undefined

-- QuickSort.Array

{-@ type Ix = Int @-}
type Ix = Int

{-@ reflect dec @-}
dec :: Ix -> Ix
dec i = i - 1

{-@ reflect inc @-}
inc :: Ix -> Ix
inc i = i + 1

{-@ type El = Int @-}
type El = Int

{-@ inline inBounds @-}
inBounds :: Ix -> Ix -> Bool
inBounds l i = 0 <= i && i < l

{-@ reflect kleisli_proto @-}
kleisli_proto :: (m b -> (b -> m c) -> m c) -> (a -> m b) -> (b -> m c) -> (a -> m c)
kleisli_proto b k1 k2 a = b (k1 a) k2

{-@
data Array m = Array
  { pureArray :: forall a. a -> m a,
    bindArray :: forall a b. m a -> (a -> m b) -> m b,
    pureBindArray :: forall a b. a:a -> k:(a -> m b) -> Equal (m b) {bindArray (pureArray a) k} {k a},
    bindPureArray :: forall a. m:m a -> Equal (m a) {bindArray m pureArray} {m},
    assocArray :: forall a b c. m:m a -> k1:(a -> m b) -> k2:(b -> m c) -> Equal (m c) {bindArray (bindArray m k1) k2} {bindArray m (kleisli_proto bindArray k1 k2)},
    lengthArray :: Ix,
    positive_lengthArray :: {0 <= lengthArray},
    readArray :: {i:Ix | inBounds lengthArray i} -> m El,
    writeArray :: {i:Ix | inBounds lengthArray i} -> El -> m Unit
  }
@-}
data Array m = Array
  { pureArray :: forall a. a -> m a,
    bindArray :: forall a b. m a -> (a -> m b) -> m b,
    pureBindArray :: forall a b. a -> (a -> m b) -> Equal (m b),
    bindPureArray :: forall a. m a -> Equal (m a),
    assocArray :: forall a b c. m a -> (a -> m b) -> (b -> m c) -> Equal (m c),
    lengthArray :: Ix,
    positive_lengthArray :: Proof,
    readArray :: Ix -> m El,
    writeArray :: Ix -> El -> m Unit
  }

-- synthetic monad functions

{-@ inline fmapArray @-}
fmapArray :: forall m a b. Array m -> (a -> b) -> m a -> m b
fmapArray _A f ma = bindArray _A ma (pureArray _A . f)

{-@ inline seqArray @-}
seqArray :: forall m a b. Array m -> m a -> m b -> m b
seqArray _A ma mb = bindArray _A ma (constant mb)

{-@ inline kleisliArray @-}
kleisliArray :: forall m a b c. Array m -> (a -> m b) -> (b -> m c) -> (a -> m c)
kleisliArray _A k1 k2 a = bindArray _A (k1 a) k2

-- congruency over monad terms

{-@
congruency_bindArray_m :: forall m a b. _A:Array m -> m1:m a -> m2:m a -> k:(a -> m b) -> Equal (m a) {m1} {m2} -> Equal (m b) {bindArray _A m1 k} {bindArray _A m2 k}
@-}
congruency_bindArray_m :: forall m a b. Array m -> m a -> m a -> (a -> m b) -> Equal (m a) -> Equal (m b)
congruency_bindArray_m _A m1 m2 k eq =
  contractability
    (bindArray _A m1)
    (bindArray _A m2)
    k
    (congruency (bindArray _A) m1 m2 eq)

{-@
congruency_bindArray_k :: forall m a b. _A:Array m -> m:m a -> k1:(a -> m b) -> k2:(a -> m b) -> Equal (a -> m b) {k1} {k2} -> Equal (m b) {bindArray _A m k1} {bindArray _A m k2}
@-}
congruency_bindArray_k :: forall m a b. Array m -> m a -> (a -> m b) -> (a -> m b) -> Equal (a -> m b) -> Equal (m b)
congruency_bindArray_k _A m k1 k2 eq = congruency (bindArray _A m) k1 k2 eq

-- inbounds
-- property that an index is inbounds of an array

{-@ inline inBoundsArray @-}
inBoundsArray :: Array m -> Ix -> Bool
inBoundsArray _A i = 0 <= i && i < lengthArray _A

-- swapArray
-- swaps two elements of an array

{-@ reflect swapArray @-}
{-@ automatic-instances swapArray @-}
{-@
swapArray :: _A:Array m -> {i:Ix | inBoundsArray _A i} -> {j:Ix | inBoundsArray _A j} -> m Unit
@-}
swapArray :: Array m -> Ix -> Ix -> m Unit
swapArray _A i j =
  (bindArray _A)
    (readArray _A i)
    (swapArray_aux1 _A i j)

{-@ reflect swapArray_aux1 @-}
{-@
swapArray_aux1 :: _A:Array m -> {i:Ix | inBoundsArray _A i} -> {j:Ix | inBoundsArray _A j} -> El -> m Unit
@-}
swapArray_aux1 :: Array m -> Ix -> Ix -> El -> m Unit
swapArray_aux1 _A i j x =
  (bindArray _A)
    (readArray _A j)
    (swapArray_aux2 _A i j x)

{-@ reflect swapArray_aux2 @-}
{-@
swapArray_aux2 :: _A:Array m -> {i:Ix | inBoundsArray _A i} -> {j:Ix | inBoundsArray _A j} -> El -> El -> m Unit
@-}
swapArray_aux2 :: Array m -> Ix -> Ix -> El -> El -> m Unit
swapArray_aux2 _A i j x y =
  (seqArray _A)
    (writeArray _A i y)
    (writeArray _A j x)

-- TODO: necessary?
-- -- checkInBounds

-- {-@ automatic-instances checkInBounds @-}
-- {-@
-- checkInBounds :: l:Ix -> i:{Ix | 0 <= i && i < l} -> {inBounds l i}
-- @-}
-- checkInBounds :: Ix -> Ix -> Proof
-- checkInBounds l i = trivial

-- -- countArray
-- -- counts the appearances of an element in an array

{-@ reflect countArray @-}
{-@ automatic-instances countArray @-}
countArray :: Array m -> El -> m Int
countArray _A e =
  if lengthArray _A <= 0
    then pureArray _A 0
    else countArray_go _A e (lengthArray _A - 1)

{-@ reflect countArray_go @-}
{-@ automatic-instances countArray_go @-}
{-@
countArray_go :: _A:Array m -> El -> i:{Ix | inBounds (lengthArray _A) i} -> m Int
@-}
countArray_go :: Array m -> El -> Ix -> m Int
countArray_go _A e i =
  (bindArray _A)
    (readArray _A i)
    (countArray_go_aux _A e i)

{-@ reflect countArray_go_aux @-}
{-@ automatic-instances countArray_go_aux @-}
{-@
countArray_go_aux :: _A:Array m -> El -> i:{Ix | inBounds (lengthArray _A) i} -> Ix -> m Int
@-}
countArray_go_aux :: Array m -> El -> Ix -> El -> m Int
countArray_go_aux _A e i x =
  if 0 < i
    then
      if e == x
        then fmapArray _A inc (countArray_go _A e (i - 1))
        else countArray_go _A e (i - 1)
    else
      if e == x
        then pureArray _A 1
        else pureArray _A 0

-- Permutation
-- the property that an array term acts as a permutation

{-@
type Permutation m A M = e:El -> Equal (m Int) {seqArray A M (countArray A e)} {countArray _A e}
@-}
type Permutation m = El -> Equal (m Int)

{-@
writeArray_decremements_countArray ::
  _A:Array m ->
  i:{Ix | inBoundsArray _A i} ->
  x:El ->
  NotEqual (m El) {readArray _A i} {pureArray _A x} ->
  Equal (m Int)
    {seqArray _A (writeArray _A i x) (countArray _A x)}
    {fmapArray _A dec (countArray _A x)}
@-}
writeArray_decremements_countArray :: Array m -> Ix -> El -> NotEqual (m El) -> Equal (m Int)
writeArray_decremements_countArray = undefined -- ! ADMITTED

-- Lemma. `swap` is a `Permutation`
-- TODO: how to use equality inside of aux function?

{-@
permutation_swap :: _A:Array m -> i:{Ix | inBoundsArray _A i} -> j:{Ix | inBoundsArray _A j} -> Permutation m {_A} {swapArray _A i j}
@-}
permutation_swap :: Array m -> Ix -> Ix -> Permutation m
permutation_swap _A i j = undefined

-- {-@
-- permutation_swap :: _A:Array m -> i:{Ix | inBoundsArray _A i} -> j:{Ix | inBoundsArray _A j} ->  -> Permutation m {_A} {swapArray _A i j}
-- @-}
