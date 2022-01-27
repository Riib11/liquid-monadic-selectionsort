{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE KindSignatures #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}

module Foo where

-- Proof

{-@
type Proof = ()
@-}
type Proof = ()

{-@ reflect unreachable @-}
-- {-@ unreachable :: {v : Proof | False} @-}
unreachable :: Proof
unreachable = ()

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

