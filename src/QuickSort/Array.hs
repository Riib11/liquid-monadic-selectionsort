{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}
{-@ LIQUID "--ple" @-}

module QuickSort.Array where

import Relation.Equality.Leibniz
import Refined.Data.Unit
import Proof

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

{-@ reflect inBounds @-}
inBounds :: Ix -> Ix -> Bool
inBounds i l = 0 <= i && i < l

{-@ reflect kleisli_proto @-}
kleisli_proto :: (m b -> (b -> m c) -> m c) -> (a -> m b) -> (b -> m c) -> (a -> m c)
kleisli_proto b k1 k2 a = b (k1 a) k2

class Array (m :: * -> *) where
  {-@ pureArray :: forall a. a -> m a @-}
  pureArray :: forall a. a -> m a

  {-@ bindArray :: forall a b. m a -> (a -> m b) -> m b @-}
  bindArray :: forall a b. m a -> (a -> m b) -> m b

  {-@
  pureBindArray :: forall a b. a:a -> k:(a -> m b) -> Equal (m b) {bindArray (pureArray a) k} {k a}
  @-}
  pureBindArray :: forall a b. a -> (a -> m b) -> Equal (m b)

  {-@
  bindPureArray :: forall a. m:m a -> Equal (m a) {bindArray m pureArray} {m}
  @-}
  bindPureArray :: forall a. m a -> Equal (m a)

  {-@
  assocArray :: forall a b c. m:m a -> k1:(a -> m b) -> k2:(b -> m c) -> Equal (m c) {bindArray (bindArray m k1) k2} {bindArray m (kleisli_proto bindArray k1 k2)}
  @-}
  assocArray :: forall a b c. m a -> (a -> m b) -> (b -> m c) -> Equal (m c)

  {-@ lengthArray :: m Ix @-}
  lengthArray :: m Ix

  {-@
  readArray ::
    i:Ix ->
    Equal (m Bool)
      {bindArray lengthArray (pureArray . inBounds i)}
      {pureArray True} ->
    m El
  @-}
  readArray :: Ix -> Equal (m Bool) -> m El

  {-@
  writeArray ::
    i:Ix ->
    Equal (m Bool)
      {bindArray lengthArray (pureArray . inBounds i)}
      {pureArray True} ->
    El ->
    m Unit
  @-}
  writeArray :: Ix -> Equal (m Bool) -> El -> m Unit

{-@
type InBounds m I = Equal (m Bool) {bindArray lengthArray (pureArray . inBounds I)} {pureArray True}
@-}
type InBounds m = Equal (m Bool)

{-@
assumeInBounds :: Array m => i:Ix -> InBounds m {i}
@-}
assumeInBounds :: Array m => Ix -> InBounds m
assumeInBounds i =
  assumeEqual
    (bindArray lengthArray (pureArray . inBounds i))
    (pureArray True)

{-@ reflect fmapArray @-}
fmapArray :: forall m a b. Array m => (a -> b) -> m a -> m b
fmapArray f ma = bindArray ma (\a -> pureArray (f a))

{-@ reflect seqArray @-}
seqArray :: forall m a b. Array m => m a -> m b -> m b
seqArray ma mb = bindArray ma (\_ -> mb)

{-@ reflect kleisliArray @-}
kleisliArray :: forall m a b c. Array m => (a -> m b) -> (b -> m c) -> (a -> m c)
kleisliArray = kleisli_proto bindArray

{-@
swapArray :: Array m => i:Ix -> InBounds m {i} -> j:Ix -> InBounds m {j} -> m Unit
@-}
swapArray :: Array m => Ix -> InBounds m -> Ix -> InBounds m -> m Unit
swapArray i iIB j jIB =
  bindArray
    (readArray i iIB)
    ( \x ->
        bindArray
          (readArray j jIB)
          ( \y ->
              seqArray
                (writeArray i iIB y)
                (writeArray j jIB x)
          )
    )

-- pure a = ma ==>
-- bind ma k = bind (pure a) k ==>
-- bind ma k = k a

-- TODO: use monad laws to prove
{-@
checkIndex :: Array m => l:Ix -> Equal (m Ix) {pureArray l} {lengthArray} -> i:{i:Ix | inBounds i l} -> InBounds m {i}
@-}
checkIndex :: Array m => Ix -> Equal (m Ix) -> Ix -> InBounds m
checkIndex l lEq i = assumeInBounds i

{-@ automatic-instances countArray @-}
countArray :: forall m. Array m => El -> m Int
countArray e =
  bindArray
    lengthArray
    ( \l ->
        countArray_go
          e
          (l - 1)
          (checkIndex l (assumeEqual (pureArray l) lengthArray) (l - 1 `by` assume (inBounds l (l - 1))))
    )

-- {-@ reflect countArray_go @-}
{-@
countArray_go :: forall m. Array m => El -> i:Ix -> InBounds m {i} -> m Int / [i]
@-}
countArray_go :: forall m. Array m => El -> Ix -> InBounds m -> m Int
countArray_go e i iIB =
  bindArray
    (readArray i iIB)
    ( \x ->
        bindArray
          lengthArray
          ( \l ->
              if 0 < i
                then
                  if e == x
                    then fmapArray (1 +) (countArray_go e (dec i) undefined)
                    else countArray_go e (dec i) undefined
                else
                  if e == x
                    then pureArray 1
                    else pureArray 0
          )
    )
