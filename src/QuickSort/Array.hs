{-@ LIQUID "--reflection" @-}

module QuickSort.Array where

import Proof
import Refined.Data.Unit
import Refined.Function
import Relation.Equality.Leibniz

type El = Int

{-@ reflect inBounds @-}
inBounds :: Int -> Int -> Bool
inBounds l i = 0 <= i && i < l

{-@ reflect kleisliArray_proto @-}
kleisliArray_proto :: (m b -> (b -> m c) -> m c) -> (a -> m b) -> (b -> m c) -> (a -> m c)
kleisliArray_proto b k1 k2 x = b (k1 x) k2

{-@ reflect seqArray_proto @-}
seqArray_proto :: (m a -> (a -> m b) -> m b) -> m a -> m b -> m b
seqArray_proto b m1 m2 = b m1 (constant m2)

{-@ reflect readReadArray_lhs @-}
readReadArray_lhs :: (m El -> (El -> m a) -> m a) -> (Int -> m El) -> Int -> (El -> El -> m a) -> m a
readReadArray_lhs b r i f = b (r i) (readReadArray_lhs_aux1 b r i f)

{-@ reflect readReadArray_lhs_aux1 @-}
readReadArray_lhs_aux1 :: (m El -> (El -> m a) -> m a) -> (Int -> m El) -> Int -> (El -> El -> m a) -> El -> m a
readReadArray_lhs_aux1 b r i f x = b (r i) (readReadArray_lhs_aux2 f x)

{-@ reflect readReadArray_lhs_aux2 @-}
readReadArray_lhs_aux2 :: (El -> El -> m a) -> El -> El -> m a
readReadArray_lhs_aux2 f x y = f x y

{-@ reflect readReadArray_rhs @-}
readReadArray_rhs :: (m El -> (El -> m a) -> m a) -> (Int -> m El) -> Int -> (El -> El -> m a) -> m a
readReadArray_rhs b r i f = b (r i) (readReadArray_rhs_aux1 f)

{-@ reflect readReadArray_rhs_aux1 @-}
readReadArray_rhs_aux1 :: (El -> El -> m a) -> El -> m a
readReadArray_rhs_aux1 f x = f x x

{-@
data Array m = Array
  { pureArray :: forall a. a -> m a,
    bindArray :: forall a b. m a -> (a -> m b) -> m b,

    pureBindArray :: forall a b. a:a -> k:(a -> m b) ->
      Equal (m b) {bindArray (pureArray a) k} {k a},
    bindPureArray :: forall a. m:m a ->
      Equal (m a) {bindArray m pureArray} {m},
    assocArray :: forall a b c. m:m a -> k1:(a -> m b) -> k2:(b -> m c) ->
      Equal (m c)
        {bindArray (bindArray m k1) k2}
        {bindArray m (kleisliArray_proto bindArray k1 k2)},

    lengthArray :: Int,
    positive_lengthArray :: {0 <= lengthArray},

    readArray :: {i:Int | inBounds lengthArray i} -> m El,
    writeArray :: {i:Int | inBounds lengthArray i} -> El -> m Unit,

    readWriteArray :: i:Int ->
      Equal (m Unit)
        {bindArray (readArray i) (writeArray i)}
        {pureArray unit},
    writeReadArray :: i:Int -> x:El ->
      Equal (m El)
        {seqArray_proto bindArray (writeArray i x) (readArray i)}
        {seqArray_proto bindArray (writeArray i x) (pureArray x)},
    writeWriteArray :: i:Int -> x:El -> y:El ->
      Equal (m Unit)
        {seqArray_proto bindArray (writeArray i x) (writeArray i y)}
        {writeArray i y},
    readReadArray :: forall a. i:Int -> f:(El -> El -> m a) ->
      Equal (m a)
        {readReadArray_lhs bindArray readArray i f}
        {readReadArray_rhs bindArray readArray i f}
  }
@-}
data Array m = Array
  { -- monad fields
    pureArray :: forall a. a -> m a,
    bindArray :: forall a b. m a -> (a -> m b) -> m b,
    -- monad laws
    pureBindArray :: forall a b. a -> (a -> m b) -> Equal (m b),
    bindPureArray :: forall a. m a -> Equal (m a),
    assocArray :: forall a b c. m a -> (a -> m b) -> (b -> m c) -> Equal (m c),
    -- array length
    lengthArray :: Int,
    positive_lengthArray :: Proof,
    -- array fields
    readArray :: Int -> m El,
    writeArray :: Int -> El -> m Unit,
    -- array laws
    readWriteArray :: Int -> Equal (m Unit),
    writeReadArray :: Int -> El -> Equal (m El),
    writeWriteArray :: Int -> El -> El -> Equal (m Unit),
    readReadArray :: forall a. Int -> (El -> El -> m a) -> Equal (m a)
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

-- inboundsArray
-- property that an index is inbounds of an array

{-@ inline inBoundsArray @-}
inBoundsArray :: Array m -> Int -> Bool
inBoundsArray _A i = 0 <= i && i < lengthArray _A

{-@ type Ix A = {i:Int | inBoundsArray _A i} @-}
type Ix = Int

-- swapArray
-- swaps two elements of an array

{-@ reflect swapArray @-}
{-@ automatic-instances swapArray @-}
{-@
swapArray :: _A:Array m -> Ix {_A} -> Ix {_A} -> m Unit
@-}
swapArray :: Array m -> Ix -> Ix -> m Unit
swapArray _A i j =
  (bindArray _A)
    (readArray _A i)
    (swapArray_aux1 _A i j)

{-@ reflect swapArray_aux1 @-}
{-@
swapArray_aux1 :: _A:Array m -> Ix {_A} -> Ix {_A} -> El -> m Unit
@-}
swapArray_aux1 :: Array m -> Ix -> Ix -> El -> m Unit
swapArray_aux1 _A i j x =
  (bindArray _A)
    (readArray _A j)
    (swapArray_aux2 _A i j x)

{-@ reflect swapArray_aux2 @-}
{-@
swapArray_aux2 :: _A:Array m -> Ix {_A} -> Ix {_A} -> El -> El -> m Unit
@-}
swapArray_aux2 :: Array m -> Ix -> Ix -> El -> El -> m Unit
swapArray_aux2 _A i j x y =
  (seqArray _A)
    (writeArray _A i y)
    (writeArray _A j x)
