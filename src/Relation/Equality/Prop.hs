module Relation.Equality.Prop where

import Proof

{-@
data EqualProp a = EqualProp
@-}
data EqualProp a = EqualProp

{-@
measure eqp :: a -> a -> Bool
@-}

{-@
type EqP a X Y = {w:EqualProp a | eqp X Y}
@-}
type EqP a = EqualProp a

{-@
assume reflexivity :: x:a -> EqP a {x} {x}
@-}
reflexivity :: a -> EqP a
reflexivity x = EqualProp

{-@
assume extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> EqP b {f x} {g x}) -> EqP (a -> b) {f} {g}
@-}
extensionality :: (a -> b) -> (a -> b) -> (a -> EqP b) -> EqP (a -> b)
extensionality f g eq = EqualProp

{-@
assume contractability :: f:(a -> b) -> g:(a -> b) -> EqP (a -> b) {f} {g} -> x:a -> EqP b {f x} {g x}
@-}
contractability :: (a -> b) -> (a -> b) -> EqP (a -> b) -> a -> EqP b
contractability f g eq x = EqualProp

{-@
assume inject :: x:a -> y:a -> {_:Proof | x == y} -> EqP a {x} {y}
@-}
inject :: a -> a -> Proof -> EqP a
inject x y eq = EqualProp

{-@
assume extract :: x:a -> y:a -> EqP a {x} {y} -> {x == y}
@-}
extract :: a -> a -> EqP a -> Proof
extract x y eq = trivial