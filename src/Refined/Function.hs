{-@ LIQUID "--reflection" @-}

module Refined.Function where

{-@ reflect identity @-}
identity :: a -> a
identity x = x

{-@ reflect constant @-}
constant :: a -> b -> a
constant a _ = a

{-@ reflect constant2 @-}
constant2 :: a -> b -> c -> a
constant2 a _ _ = a