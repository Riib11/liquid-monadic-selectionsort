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
assume :: b:Bool -> {b == True}
@-}
assume :: Bool -> Proof
assume b = undefined

-- {-@
-- assert :: b:Bool -> {}
-- @-}
-- assert ::
