module Relation.Equality.Leibniz where

import Proof

{-@
type Equal a X Y = pr:(a -> Bool) -> {pr X = pr Y}
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
inject :: x:a -> y:a -> {_:Proof | x == y} -> Equal a {x} {y}
@-}
inject :: a -> a -> Proof -> Equal a
inject x y eq = reflexivity (x `by` eq)

{-@
assume extract :: x:a -> y:a -> Equal a {x} {y} -> {x == y}
@-}
extract :: a -> a -> Equal a -> Proof
extract x y eq = trivial
