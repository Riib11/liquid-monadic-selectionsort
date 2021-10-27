module Proof where

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

{-@ reflect by @-}
by :: a -> Proof -> a
by x _ = x

{-@ reflect with @-}
with :: a -> b -> a
with x _ = x

-- assumptions

{-@
assume
assume_eq :: x:Int -> y:Int -> {x == y}
@-}
assume_eq :: Int -> Int -> Proof
assume_eq x y = trivial

{-@
assume
assume_le :: x:Int -> y:Int -> {x <= y}
@-}
assume_le :: Int -> Int -> Proof
assume_le x y = trivial

{-@
assume
assume_lt :: x:Int -> y:Int -> {x < y}
@-}
assume_lt :: Int -> Int -> Proof
assume_lt x y = trivial

{-@
assume
assume_true :: b:Bool -> {b == True}
@-}
assume_true :: Bool -> Proof
assume_true b = trivial
