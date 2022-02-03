{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--compile-spec" @-}

module Relation.Equality.Prop where

import Proof

{-@
data Equality a = Equality
@-}
data Equality a = Equality

{-@
measure eqp :: a -> a -> Bool
@-}

{-@
type Equal a X Y = {w:Equality a | eqp X Y}
@-}
type Equal a = Equality a

{-@
assume reflexivity :: x:a -> Equal a {x} {x}
@-}
reflexivity :: a -> Equal a
reflexivity x = Equality

{-@
assume extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> Equal b {f x} {g x}) -> Equal (a -> b) {f} {g}
@-}
extensionality :: (a -> b) -> (a -> b) -> (a -> Equal b) -> Equal (a -> b)
extensionality f g eq = Equality

{-@
assume contractability :: f:(a -> b) -> g:(a -> b) -> Equal (a -> b) {f} {g} -> x:a -> Equal b {f x} {g x}
@-}
contractability :: (a -> b) -> (a -> b) -> Equal (a -> b) -> a -> Equal b
contractability f g eq x = Equality

{-@
assume inject :: x:a -> y:a -> {_:Proof | x == y} -> Equal a {x} {y}
@-}
inject :: a -> a -> Proof -> Equal a
inject x y eq = Equality

{-@
assume extract :: x:a -> y:a -> Equal a {x} {y} -> {x == y}
@-}
extract :: a -> a -> Equal a -> Proof
extract x y eq = trivial
