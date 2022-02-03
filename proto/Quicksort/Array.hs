{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}
{-@ LIQUID "--ple-local" @-}
-- {-@ LIQUID "--short-names" @-}

module QuickSort.Array where

-- -- Proof

-- {-@
-- type Proof = ()
-- @-}
-- type Proof = ()

-- {-@ reflect unreachable @-}
-- -- {-@ unreachable :: {v : Proof | False} @-}
-- unreachable :: Proof
-- unreachable = ()

-- {-@ reflect trivial @-}
-- trivial :: Proof
-- trivial = ()

-- {-@ reflect refinement @-}
-- refinement :: a -> Proof
-- refinement _ = trivial

-- {-@ reflect by @-}
-- by :: a -> Proof -> a
-- by x _ = x

-- {-@ reflect by @-}
-- by_refinement :: a -> b -> a
-- by_refinement x y = x `by` refinement y

-- {-@
-- assume :: b:Bool -> {b}
-- @-}
-- assume :: Bool -> Proof
-- assume b = undefined

-- {-@ reflect begin @-}
-- begin :: a -> Proof
-- begin _ = trivial

-- infixl 3 ===

-- {-@ infixl 3 === @-}
-- {-@ reflect === @-}
-- {-@
-- (===) :: x:a -> y:{a | y == x} -> z:{a | z == x && z == y}
-- @-}
-- (===) :: a -> a -> a
-- x === y = y

-- -- Refined.Data.Unit

{-@
type Unit = ()
@-}
type Unit = ()

-- {-@ reflect unit @-}
-- unit :: Unit
-- unit = ()

-- -- Function

-- {-@ reflect constant @-}
-- constant :: a -> b -> a
-- constant a _ = a

-- -- Relation.Equality.Leibniz

-- {-@
-- type Equal a X Y = prop:(a -> Bool) -> {prop X = prop Y}
-- @-}
-- type Equal a = (a -> Bool) -> Proof

-- {-@
-- type NotEqual a X Y = Equal a X Y -> {False}
-- @-}
-- type NotEqual a = Equal a -> Proof

-- {-@
-- reflexivity :: x:a -> Equal a {x} {x}
-- @-}
-- reflexivity :: a -> Equal a
-- reflexivity a pr = trivial

-- {-@
-- symmetry :: x:a -> y:a -> Equal a {x} {y} -> Equal a {y} {x}
-- @-}
-- symmetry :: a -> a -> Equal a -> Equal a
-- symmetry x y eq_x_y = undefined

-- {-@
-- transitivity :: x:a -> y:a -> z:a -> Equal a {x} {y} -> Equal a {y} {z} -> Equal a {x} {z}
-- @-}
-- transitivity :: a -> a -> a -> Equal a -> Equal a -> Equal a
-- transitivity x y z eq_x_y eq_y_z = undefined

-- {-@
-- congruency :: f:(a -> b) -> x:a -> y:a -> Equal a {x} {y} -> Equal b {f x} {f y}
-- @-}
-- congruency :: (a -> b) -> a -> a -> Equal a -> Equal b
-- congruency f x y eq_x_y = undefined

-- {-@
-- assume extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> Equal b {f x} {g x}) -> Equal (a -> b) {f} {g}
-- @-}
-- extensionality :: (a -> b) -> (a -> b) -> (a -> Equal b) -> Equal (a -> b)
-- extensionality f g eq pr = trivial

-- {-@
-- assume contractability :: f:(a -> b) -> g:(a -> b) -> x:a -> Equal (a -> b) {f} {g} -> Equal b {f x} {g x}
-- @-}
-- contractability :: (a -> b) -> (a -> b) -> a -> Equal (a -> b) -> Equal b
-- contractability f g eq a pr = trivial

-- {-@
-- inject :: forall a. x:a -> y:{y:a | x = y} -> Equal a {x} {y}
-- @-}
-- inject :: forall a. a -> a -> Equal a
-- inject x y = reflexivity x

-- {-@
-- assume extract :: x:a -> y:a -> Equal a {x} {y} -> {x == y}
-- @-}
-- extract :: a -> a -> Equal a -> Proof
-- extract x y eq = trivial

-- {-@
-- assumeEqual :: x:a -> y:a -> Equal a {x} {y}
-- @-}
-- assumeEqual :: a -> a -> Equal a
-- assumeEqual _ _ = undefined

-- QuickSort.Array

{-@ reflect lengthArray @-}
lengthArray :: Ix
lengthArray = 10

{-@
type Ix = {i:Int | 0 <= i && i < 10}
@-}
type Ix = Int

{-@ type El = Int @-}
type El = Int

-- {-@ reflect dec @-}
-- dec :: Ix -> Ix
-- dec i = i - 1

-- {-@ reflect inc @-}
-- inc :: Ix -> Ix
-- inc i = i + 1

-- {-@ reflect kleisli_proto @-}
-- kleisli_proto :: (m b -> (b -> m c) -> m c) -> (a -> m b) -> (b -> m c) -> (a -> m c)
-- kleisli_proto b k1 k2 a = b (k1 a) k2

class Array (m :: * -> *) where
  -- -- monad fields

  -- {-@ pureArray :: forall a. a -> m a @-}
  -- pureArray :: forall a. a -> m a

  -- {-@ bindArray :: forall a b. m a -> (a -> m b) -> m b @-}
  -- bindArray :: forall a b. m a -> (a -> m b) -> m b

  -- -- monad laws

  -- {-@
  -- pureBindArray :: forall a b. a:a -> k:(a -> m b) -> Equal (m b) {bindArray (pureArray a) k} {k a}
  -- @-}
  -- pureBindArray :: forall a b. a -> (a -> m b) -> Equal (m b)

  -- {-@
  -- bindPureArray :: forall a. m:m a -> Equal (m a) {bindArray m pureArray} {m}
  -- @-}
  -- bindPureArray :: forall a. m a -> Equal (m a)

  -- {-@
  -- assocArray :: forall a b c. m:m a -> k1:(a -> m b) -> k2:(b -> m c) -> Equal (m c) {bindArray (bindArray m k1) k2} {bindArray m (kleisli_proto bindArray k1 k2)}
  -- @-}
  -- assocArray :: forall a b c. m a -> (a -> m b) -> (b -> m c) -> Equal (m c)

  -- array fields

  {-@
  readArray :: i:{Int | True} -> m El
  @-}
  readArray :: Ix -> m El

-- {-@
-- writeArray :: Ix -> El -> m Unit
-- @-}
-- writeArray :: Ix -> El -> m Unit

-- -- array laws
-- -- TODO

{-@
readWriteArray :: i:Ix ->
  Equal (m Unit)
    {bindArray (readArray i) (writeArray i)}
    {pureArray unit}
@-}
readWriteArray :: Ix -> Equal (m Unit)
{-@
writeReadArray :: i:Ix -> x:El ->
  Equal (m El)
    {bindArray (writeArray i x) (constant (readArray i))}
    {bindArray (writeArray i x) (constant (pureArray x))}
@-}
writeReadArray :: Ix -> El -> Equal (m El)

-- {-@
-- writeWriteArray :: i:Ix -> x:El -> y:El ->
--   Equal (m Unit)
--     {bindArray (writeArray i x) (constant (writeArray i y))}
--     {bindArray (writeArray i y)}
-- @-}
-- writeWriteArray :: Ix -> El -> El -> Equal (m Unit)

-- {-@
-- readReadArray :: i:Ix -> f:(El -> El -> m a) ->
--   Equal (m a)
--     {readReadArray_aux1 bindArray readArray i f}
--     {readReadArray_aux1 bindArray readArray i f}
-- @-}
-- readReadArray :: Ix -> (El -> El -> m a) -> Equal (m a)

-- {-@ reflect readReadArray_aux1 @-}
-- readReadArray_aux1 ::
--   (m El -> (El -> m a) -> m a) ->
--   (Ix -> m El) ->
--   Ix ->
--   (El -> El -> m a) ->
--   m a
-- readReadArray_aux1 b r i f = b (r i) (readReadArray_aux1_aux1 b r i f)

-- {-@ reflect readReadArray_aux1_aux1 @-}
-- readReadArray_aux1_aux1 ::
--   (m El -> (El -> m a) -> m a) ->
--   (Ix -> m El) ->
--   Ix ->
--   (El -> El -> m a) ->
--   El ->
--   m a
-- readReadArray_aux1_aux1 b r i f x = b (r i) (readReadArray_aux1_aux2 f x)

-- {-@ reflect readReadArray_aux1_aux2 @-}
-- readReadArray_aux1_aux2 :: (El -> El -> m a) -> El -> El -> m a
-- readReadArray_aux1_aux2 f x y = f x y

-- {-@ reflect readReadArray_aux2 @-}
-- readReadArray_aux2 ::
--   (m El -> (El -> m a) -> m a) -> (Ix -> m El) -> Ix -> (El -> El -> m a) -> m a
-- readReadArray_aux2 b r i f = b (r i) (readReadArray_aux2_aux f)

-- {-@ reflect readReadArray_aux2_aux @-}
-- readReadArray_aux2_aux :: (El -> El -> m a) -> El -> m a
-- readReadArray_aux2_aux f x = f x x

-- -- assumptions

-- {-@
-- writeWriteArray :: Array m => i:Ix -> x:El -> y:El ->
--   Equal (m Unit)
--     {bindArray (writeArray i x) (constant (writeArray i y))}
--     {writeArray i y}
-- @-}
-- writeWriteArray :: Array m => Ix -> El -> El -> Equal (m Unit)
-- writeWriteArray i x y = undefined -- ! ASSUMED

-- {-@
-- readReadArray :: Array m => i:Ix -> f:(El -> El -> m a) ->
--   Equal (m a)
--     {bindArray (readArray i) (readReadArray_aux1 i f)}
--     {bindArray (readArray i) (readReadArray_aux2 f)}
-- @-}
-- readReadArray :: Array m => Ix -> (El -> El -> m a) -> Equal (m a)
-- readReadArray i f = undefined -- ! ASSUMED

-- {-@ reflect readReadArray_aux1 @-}
-- readReadArray_aux1 :: Array m => Ix -> (El -> El -> m a) -> El -> m a
-- readReadArray_aux1 i f x =
--   bindArray
--     (readArray i)
--     (readReadArray_aux1_aux f x)

-- {-@ reflect readReadArray_aux1_aux @-}
-- readReadArray_aux1_aux :: Array m => (El -> El -> m a) -> El -> El -> m a
-- readReadArray_aux1_aux f x x' = f x x'

-- {-@ reflect readReadArray_aux2 @-}
-- readReadArray_aux2 :: Array m => (El -> El -> m a) -> El -> m a
-- readReadArray_aux2 f x = f x x

-- -- synthetic monad functions

-- {-@ reflect fmapArray @-}
-- fmapArray :: forall m a b. Array m => (a -> b) -> m a -> m b
-- fmapArray f ma = bindArray ma (pureArray . f)

-- {-@ reflect seqArray @-}
-- seqArray :: forall m a b. Array m => m a -> m b -> m b
-- seqArray ma mb = bindArray ma (constant mb)

-- {-@ reflect kleisliArray @-}
-- kleisliArray :: forall m a b c. Array m => (a -> m b) -> (b -> m c) -> (a -> m c)
-- kleisliArray k1 k2 a = bindArray (k1 a) k2

-- -- congruency over monad terms

-- {-@
-- congruency_bindArray_m :: forall m a b. Array m => m1:m a -> m2:m a -> k:(a -> m b) -> Equal (m a) {m1} {m2} -> Equal (m b) {bindArray m1 k} {bindArray m2 k}
-- @-}
-- congruency_bindArray_m :: forall m a b. Array m => m a -> m a -> (a -> m b) -> Equal (m a) -> Equal (m b)
-- congruency_bindArray_m m1 m2 k eq =
--   contractability
--     (bindArray m1)
--     (bindArray m2)
--     k
--     (congruency bindArray m1 m2 eq)

-- {-@
-- congruency_bindArray_k :: forall m a b. Array m => m:m a -> k1:(a -> m b) -> k2:(a -> m b) -> Equal (a -> m b) {k1} {k2} -> Equal (m b) {bindArray m k1} {bindArray m k2}
-- @-}
-- congruency_bindArray_k :: forall m a b. Array m => m a -> (a -> m b) -> (a -> m b) -> Equal (a -> m b) -> Equal (m b)
-- congruency_bindArray_k m k1 k2 eq = congruency (bindArray m) k1 k2 eq

-- -- swapArray
-- -- swaps two elements of an array

-- {-@
-- swapArray :: Array m => i:Ix -> j:Ix -> m Unit
-- @-}
-- swapArray :: Array m => Ix -> Ix -> m Unit
-- swapArray i j =
--   bindArray
--     (readArray i)
--     ( \x ->
--         bindArray
--           (readArray j)
--           ( \y ->
--               seqArray
--                 (writeArray i y)
--                 (writeArray j x)
--           )
--     )

-- {-@ reflect countArray @-}
-- countArray :: Array m => El -> m Int
-- countArray e = countArray_go e (lengthArray - 1)

-- {-@ reflect countArray_go @-}
-- {-@
-- countArray_go :: Array m => e:El -> i:Ix -> m Int / [i]
-- @-}
-- countArray_go :: Array m => El -> Ix -> m Int
-- countArray_go e i =
--   bindArray
--     (readArray i)
--     ( \x ->
--         if 0 < i
--           then
--             if e == x
--               then fmapArray inc (countArray_go e (dec i))
--               else countArray_go e (dec i)
--           else
--             if e == x
--               then pureArray 1
--               else pureArray 0
--     )

-- -- Permutation
-- -- the property that an array term acts as a permutation

-- {-@
-- type Permutation m M = e:El -> Equal (m Int) {seqArray M (countArray e)} {countArray e}
-- @-}
-- type Permutation m = El -> Equal (m Int)

-- {-@
-- writeArray_countArray ::
--   Array m =>
--   i:Ix ->
--   x:El ->
--   Equal (m Bool)
--     {bindArray (readArray i) (writeArray_countArray_aux x)}
--     {pureArray False} ->
--   Equal (m Int)
--     {seqArray (writeArray i x) (countArray x)}
--     {fmapArray dec (countArray x)}
-- @-}
-- writeArray_countArray ::
--   Array m =>
--   Ix ->
--   El ->
--   Equal (m Bool) ->
--   Equal (m Int)
-- writeArray_countArray = undefined -- ! ADMITTED
-- {-
-- seqArray (writeArray i x) (countArray x)
-- bindArray (writeArray i x) (\_ -> countArray x)
-- bindArray (writeArray i x) (\_ -> countArray x)

-- bindArray (countArray_go x) (\c -> dec c)
-- bindArray (countArray x) (\c -> dec c)
-- fmapArray dec (countArray x)
-- -}

-- {-@ reflect writeArray_countArray_aux @-}
-- writeArray_countArray_aux :: Array m => El -> El -> m Bool
-- writeArray_countArray_aux x y = pureArray (x == y)
