module Relation.Equality.Leibniz where

import Proof

-- do I need this?
-- {-@
-- measure eqL :: a -> a -> Bool
-- @-}

{-@
type EqL a X Y = pr:(a -> Bool) -> {pr X == pr Y}
@-}
type EqL a = (a -> Bool) -> Proof

{-@
reflexivity :: x:a -> EqL a {x} {x}
@-}
reflexivity :: a -> EqL a
reflexivity a pr = trivial

{-@
assume extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> EqL b {f x} {g x}) -> EqL (a -> b) {f} {g}
@-}
extensionality :: (a -> b) -> (a -> b) -> (a -> EqL b) -> EqL (a -> b)
extensionality f g eq pr = trivial
 
{-@
assume contractability :: f:(a -> b) -> g:(a -> b) -> EqL (a -> b) {f} {g} -> x:a -> EqL b {f x} {g x}
@-}
contractability :: (a -> b) -> (a -> b) -> EqL (a -> b) -> a -> EqL b
contractability f g eq a pr = trivial

{-@
inject :: x:a -> y:a -> {_:Proof | x == y} -> EqL a {x} {y}
@-}
inject :: a -> a -> Proof -> EqL a
inject x y eq = reflexivity (x `by` eq)

{-@
assume extract :: x:a -> y:a -> EqL a {x} {y} -> {x == y}
@-}
extract :: a -> a -> EqL a -> Proof
extract x y eq = trivial