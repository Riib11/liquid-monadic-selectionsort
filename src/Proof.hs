module Proof where


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


{-@ reflect by @-}
{-@ by :: x:a -> b -> {x':a | x' = x} @-}
by :: a -> b -> a
by x _ = x
