{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}

module Foo where

class C t where
  {-@
  f :: t -> t
  @-}
  f :: t -> t

  {-@ law :: x:t -> {f x == f (f x)} @-}
  law :: t -> ()

{-@
lem :: C t => x:t -> {f x = f (f x)}
@-}
lem :: C t => t -> ()
lem x = law x
