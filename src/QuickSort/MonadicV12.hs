{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}
{-@ LIQUID "--ple" @-}

module QuickSort.MonadicV12 where

{-@ type Proof = () @-}
type Proof = ()

{-@ reflect trivial @-}
trivial :: Proof
trivial = ()

{-@ reflect by @-}
by :: a -> b -> a
by a _ = a

{-@
assume :: b:Bool -> {b = True}
@-}
assume :: Bool -> Proof
assume _ = undefined

{-@ type Unit = () @-}
type Unit = ()

{-@ reflect unit @-}
unit :: Unit
unit = ()

{-@
type Equal a X Y = prop:(a -> Bool) -> {prop X = prop Y}
@-}
type Equal a = (a -> Bool) -> Proof

{-@
toEqual :: x:a -> y:{y:a | x = y} -> Equal a {x} {y}
@-}
toEqual :: a -> a -> Equal a
toEqual x y prop = trivial

{-@
assumeEqual :: x:a -> y:a -> Equal a {x} {y}
@-}
assumeEqual :: a -> a -> Equal a
assumeEqual _ _ = undefined

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

class Array (m :: * -> *) where
  {-@ pureArray :: forall a. a -> m a @-}
  pureArray :: forall a. a -> m a

  {-@ bindArray :: forall a b. m a -> (a -> m b) -> m b @-}
  bindArray :: forall a b. m a -> (a -> m b) -> m b

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
          (checkIndex l undefined (l - 1 `by` assume (inBounds l (l - 1))))
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
