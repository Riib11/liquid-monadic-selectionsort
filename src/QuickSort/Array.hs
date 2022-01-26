{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}
{-@ LIQUID "--ple-local" @-}

module QuickSort.Array where

-- Proof

{-@
type Proof = ()
@-}
type Proof = ()

{-@ reflect unreachable @-}
-- {-@ unreachable :: {v : Proof | False} @-}
unreachable :: Proof
unreachable = ()

{-@ reflect impossible @-}
{-@
impossible :: {_:a | False} -> a
@-}
impossible :: a -> a
impossible x = x

{-@ reflect trivial @-}
trivial :: Proof
trivial = ()

{-@ reflect refinement @-}
refinement :: a -> Proof
refinement _ = trivial

{-@ reflect by @-}
by :: a -> Proof -> a
by x _ = x

{-@ reflect by @-}
by_refinement :: a -> b -> a
by_refinement x y = x `by` refinement y

{-@
assume :: b:Bool -> {b}
@-}
assume :: Bool -> Proof
assume b = undefined

{-@ reflect begin @-}
begin :: a -> Proof
begin _ = trivial

infixl 3 ===

{-@ infixl 3 === @-}
{-@ reflect === @-}
{-@
(===) :: x:a -> y:{a | y == x} -> z:{a | z == x && z == y}
@-}
(===) :: a -> a -> a
x === y = y

-- Refined.Data.Unit

{-@
type Unit = ()
@-}
type Unit = ()

{-@ reflect unit @-}
unit :: Unit
unit = ()

-- Relation.Equality.Leibniz

{-@
type Equal a X Y = prop:(a -> Bool) -> {prop X = prop Y}
@-}
type Equal a = (a -> Bool) -> Proof

{-@
reflexivity :: x:a -> Equal a {x} {x}
@-}
reflexivity :: a -> Equal a
reflexivity a pr = trivial

{-@
assume extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> Equal b {f x} {g x}) -> Equal (a -> b) {f} {g}
@-}
extensionality :: (a -> b) -> (a -> b) -> (a -> Equal b) -> Equal (a -> b)
extensionality f g eq pr = trivial

{-@
assume contractability :: f:(a -> b) -> g:(a -> b) -> Equal (a -> b) {f} {g} -> x:a -> Equal b {f x} {g x}
@-}
contractability :: (a -> b) -> (a -> b) -> Equal (a -> b) -> a -> Equal b
contractability f g eq a pr = trivial

{-@
inject :: forall a. x:a -> y:{y:a | x = y} -> Equal a {x} {y}
@-}
inject :: forall a. a -> a -> Equal a
inject x y = reflexivity x 

{-@
assume extract :: x:a -> y:a -> Equal a {x} {y} -> {x == y}
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
